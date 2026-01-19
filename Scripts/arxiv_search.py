#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = ["requests", "pypdf"]
# ///

from __future__ import annotations

import argparse
import datetime as dt
import io
import json
from pathlib import Path
import sys
import urllib.parse
import xml.etree.ElementTree as ET

import requests
from pypdf import PdfReader


ATOM_NS = {
    "atom": "http://www.w3.org/2005/Atom",
    "arxiv": "http://arxiv.org/schemas/atom",
}


def arxiv_api_url(
    *,
    query: str,
    categories: list[str],
    start: int,
    max_results: int,
    sort_by: str,
    sort_order: str,
) -> str:
    # arXiv API expects `search_query=...` with terms like `all:foo` and `cat:math.NT`.
    q_parts: list[str] = []
    if query.strip():
        q_parts.append(f"all:{query.strip()}")
    cats = [c.strip() for c in categories if c.strip()]
    if cats:
        # arXiv category is a single primary category; AND-ing multiple categories returns nothing.
        # The API supports `OR` in the query language; keep it simple (no parentheses).
        cat_expr = " OR ".join([f"cat:{c}" for c in cats])
        q_parts.append(cat_expr)
    if not q_parts:
        q_parts = ["all:Lean"]

    params = {
        "search_query": " AND ".join(q_parts),
        "start": str(start),
        "max_results": str(max_results),
        "sortBy": sort_by,
        "sortOrder": sort_order,
    }
    return "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(params)


def parse_atom(xml_text: str) -> list[dict[str, str]]:
    root = ET.fromstring(xml_text)
    out: list[dict[str, str]] = []
    for entry in root.findall("atom:entry", ATOM_NS):
        title = (entry.findtext("atom:title", default="", namespaces=ATOM_NS) or "").strip()
        summary = (entry.findtext("atom:summary", default="", namespaces=ATOM_NS) or "").strip()
        published = (entry.findtext("atom:published", default="", namespaces=ATOM_NS) or "").strip()

        # Prefer the canonical arXiv abstract page link.
        abs_url = ""
        pdf_url = ""
        for link in entry.findall("atom:link", ATOM_NS):
            href = (link.attrib.get("href") or "").strip()
            rel = (link.attrib.get("rel") or "").strip()
            typ = (link.attrib.get("type") or "").strip()
            if rel == "alternate" and href:
                abs_url = href
            if typ == "application/pdf" and href:
                pdf_url = href

        cats = [c.attrib.get("term", "") for c in entry.findall("atom:category", ATOM_NS)]
        out.append(
            {
                "title": title,
                "published": published,
                "categories": ", ".join([c for c in cats if c]),
                "url": abs_url,
                "pdf_url": pdf_url,
                "summary": summary,
            }
        )
    return out


def default_cache_dir() -> Path:
    return Path.home() / ".cache" / "covolume" / "arxiv"


def cache_key_from_pdf_url(pdf_url: str) -> str:
    # Example: https://arxiv.org/pdf/2601.03768v1  -> 2601.03768v1
    tail = pdf_url.rstrip("/").split("/")[-1]
    return tail.replace(".pdf", "")


def main() -> int:
    ap = argparse.ArgumentParser(description="Tiny arXiv search (newest-first).")
    ap.add_argument("query", nargs="?", default="", help="Free-text query (matches title/abs).")
    ap.add_argument("--cat", action="append", default=[], help="Category filter, e.g. math.NT (repeatable).")
    ap.add_argument("--n", type=int, default=10, help="Max results to fetch (default: 10).")
    ap.add_argument("--id", default="", help="Fetch a specific arXiv id (e.g. 2601.03768 or 2601.03768v1).")
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON (still bounded; PDF text is optional).",
    )
    ap.add_argument(
        "--sort-by",
        default="submittedDate",
        choices=["relevance", "lastUpdatedDate", "submittedDate"],
        help="arXiv sort key (default: submittedDate).",
    )
    ap.add_argument(
        "--sort-order",
        default="descending",
        choices=["ascending", "descending"],
        help="Sort order (default: descending).",
    )
    ap.add_argument("--timeout-s", type=int, default=20)
    ap.add_argument(
        "--pdf-text",
        action="store_true",
        help="Download PDFs and print extracted text snippets (bounded).",
    )
    ap.add_argument("--pdf-pages", type=int, default=2, help="Max pages to extract per PDF (default: 2).")
    ap.add_argument(
        "--pdf-max-chars",
        type=int,
        default=6000,
        help="Max extracted characters to print per PDF (default: 6000).",
    )
    ap.add_argument("--cache-dir", default="", help="Cache directory for downloaded PDFs.")
    ap.add_argument("--no-cache", action="store_true", help="Disable PDF caching.")
    args = ap.parse_args()

    n = max(1, min(args.n, 50))
    if args.id.strip():
        # Use arXiv API `id_list` for exact lookup.
        params = {"id_list": args.id.strip()}
        url = "https://export.arxiv.org/api/query?" + urllib.parse.urlencode(params)
    else:
        url = arxiv_api_url(
            query=args.query,
            categories=args.cat,
            start=0,
            max_results=n,
            sort_by=args.sort_by,
            sort_order=args.sort_order,
        )

    r = requests.get(url, timeout=args.timeout_s)
    r.raise_for_status()
    papers = parse_atom(r.text)

    now = dt.datetime.now(dt.timezone.utc).isoformat()
    if args.json:
        out: dict[str, object] = {
            "time": now,
            "query": args.query,
            "categories": list(args.cat),
            "sort_by": args.sort_by,
            "sort_order": args.sort_order,
            "n": n,
            "results": [],
        }
    else:
        print(f"arxiv_search time={now}")
        print(f"query={args.query!r} categories={args.cat} sort={args.sort_by}:{args.sort_order} n={n}")
        print("")

    cache_dir = Path(args.cache_dir).expanduser() if args.cache_dir.strip() else default_cache_dir()
    for i, p in enumerate(papers, start=1):
        item: dict[str, object] = dict(p)
        item["rank"] = i
        item["pdf_text"] = None

        if args.pdf_text and p.get("pdf_url"):
            pdf_url = p["pdf_url"]
            try:
                cache_dir.mkdir(parents=True, exist_ok=True)
                key = cache_key_from_pdf_url(pdf_url)
                cache_path = cache_dir / f"{key}.pdf"
                pdf_bytes: bytes
                if (not args.no_cache) and cache_path.exists() and cache_path.is_file():
                    pdf_bytes = cache_path.read_bytes()
                else:
                    pr = requests.get(pdf_url, timeout=args.timeout_s)
                    pr.raise_for_status()
                    pdf_bytes = pr.content
                    if not args.no_cache:
                        cache_path.write_bytes(pdf_bytes)

                reader = PdfReader(io.BytesIO(pdf_bytes))
                pages = max(0, min(int(args.pdf_pages), len(reader.pages)))
                txt_parts: list[str] = []
                for j in range(pages):
                    t = (reader.pages[j].extract_text() or "").strip()
                    if t:
                        txt_parts.append(t)
                txt = "\n\n".join(txt_parts).strip()
                if txt:
                    if len(txt) > int(args.pdf_max_chars):
                        txt = txt[: int(args.pdf_max_chars)].rstrip() + "…"
                    item["pdf_text"] = txt
                else:
                    item["pdf_text"] = ""
            except Exception as e:
                item["pdf_text"] = f"(failed to fetch/parse: {type(e).__name__}: {e})"

        if args.json:
            out["results"].append(item)
            continue

        print(f"{i}. {p['title']}")
        print(f"   published: {p['published']}")
        if p["categories"]:
            print(f"   categories: {p['categories']}")
        if p["url"]:
            print(f"   url: {p['url']}")
        if p["pdf_url"]:
            print(f"   pdf: {p['pdf_url']}")
        # Keep summaries short by default.
        if p["summary"]:
            s = p["summary"].replace("\n", " ").strip()
            if len(s) > 240:
                s = s[:240].rstrip() + "…"
            print(f"   summary: {s}")
        if args.pdf_text:
            if item["pdf_text"] is None:
                print("   pdf_text: (no pdf link)")
            elif item["pdf_text"] == "":
                print("   pdf_text: (no extractable text on first pages)")
            else:
                print("   pdf_text:")
                print("     [note: extracted text can be noisy; validate before using as evidence]")
                for line in str(item["pdf_text"]).splitlines():
                    print(f"     {line}")
        print("")

    if args.json:
        json.dump(out, sys.stdout, ensure_ascii=False, indent=2)
        sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

