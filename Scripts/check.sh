#!/usr/bin/env bash
set -euo pipefail

# Single entrypoint for local + CI checks.
#
# Profiles:
#   ./Scripts/check.sh pre-commit
#   ./Scripts/check.sh pre-push
#   ./Scripts/check.sh ci [--github]
#
# Philosophy:
# - Use the same entrypoint everywhere.
# - Keep pre-commit fast (no full build).
# - Put “CI-likeness” in pre-push and CI profiles.

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

# `lake` may not be on PATH in non-interactive shells.
LAKE="${LAKE:-}"
if [[ -z "$LAKE" ]]; then
  if [[ -x "$HOME/.elan/bin/lake" ]]; then
    LAKE="$HOME/.elan/bin/lake"
  else
    LAKE="lake"
  fi
fi

profile="${1:-}"
shift || true

github=0
for arg in "$@"; do
  case "$arg" in
    --github) github=1 ;;
    *) ;;
  esac
done

lint_style_args=()
if [[ "$github" -eq 1 ]]; then
  lint_style_args+=(--github)
fi

# Optional helper CLI (no local/sibling repo assumptions).
#
# If installed, `proofpatch` can:
# - generate a bounded HTML proof-frontier snapshot
# - run a bounded `review-diff`
#
# Override with PROOFPATCH_BIN=/path/to/proofpatch.
PROOFPATCH_BIN="${PROOFPATCH_BIN:-}"
if [[ -z "$PROOFPATCH_BIN" ]]; then
  if command -v proofpatch >/dev/null 2>&1; then
    PROOFPATCH_BIN="proofpatch"
  fi
fi

case "$profile" in
  pre-commit)
    echo "[check:pre-commit] gon_checks"
    "$LAKE" exe gon_checks

    # A small compilation smoke test: catch obvious breakage early without rebuilding everything.
    #
    # This is intentionally narrower than `lake build` (which is reserved for pre-push).
    # Opt out with `GON_PRECOMMIT_BUILD=0` if you need a very fast inner loop.
    precommit_build="${GON_PRECOMMIT_BUILD:-1}"
    if [[ "$precommit_build" != "0" ]]; then
      echo "[check:pre-commit] lake build (smoke: key entrypoints)"
      "$LAKE" build GeometryOfNumbers Covolume.Legendre.Main Covolume.Cauchy.Main

      # After a successful smoke build, emit a compact, structured summary of the current proof
      # frontier when `proofpatch` is available.
      precommit_summary="${GON_PRECOMMIT_SUMMARY:-1}"
      if [[ "$precommit_summary" != "0" ]]; then
        if [[ -z "$PROOFPATCH_BIN" ]]; then
          echo "[check:pre-commit] proofpatch not available; skipping proof frontier summary" >&2
        else
          echo "[check:pre-commit] proof frontier summary (proofpatch report)"
          mkdir -p tmp/proofpatch
          out_html="${GON_PRECOMMIT_REPORT_HTML:-tmp/proofpatch/status.html}"
          files=(
            "Covolume/Legendre/Main.lean"
            "Covolume/Cauchy/Main.lean"
          )
          "$PROOFPATCH_BIN" report --repo "$repo_root" --files "${files[@]}" \
            --timeout-s 60 --max-sorries 50 --context-lines 1 \
            --output-html "$out_html" || true
        fi
      fi
    else
      echo "[check:pre-commit] lake build skipped (GON_PRECOMMIT_BUILD=0)" >&2
    fi

    echo "[check:pre-commit] lint-style (fast)"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}" --fast

    llm_on="${GON_LLM_REVIEW:-${COVOLUME_LLM_REVIEW:-1}}"
    if [[ "$llm_on" != "0" ]]; then
      echo "[check:pre-commit] llm-review (default on; set GON_LLM_REVIEW=0 to disable)"
      set +e

      strict="${GON_LLM_REVIEW_STRICT:-${COVOLUME_LLM_REVIEW_STRICT:-0}}"
      req=()
      if [[ "$strict" != "0" ]]; then
        req+=(--require-key)
      fi

      if [[ -z "$PROOFPATCH_BIN" ]]; then
        if [[ "$strict" != "0" ]]; then
          echo "[check:pre-commit] proofpatch not available (install proofpatch or set PROOFPATCH_BIN)" >&2
          exit 1
        else
          echo "[check:pre-commit] proofpatch not available; skipping llm-review" >&2
          set -e
          true
        fi
      fi

      if [[ -n "$PROOFPATCH_BIN" ]]; then
        mkdir -p tmp/proofpatch
        out_json="${GON_LLM_REVIEW_JSON:-tmp/proofpatch/review-diff.json}"
        "$PROOFPATCH_BIN" review-diff --repo "$repo_root" --scope staged "${req[@]+"${req[@]}"}" --output-json "$out_json"

        rc=$?
        set -e
        if [[ $rc -ne 0 ]]; then
          if [[ "$strict" != "0" ]]; then
            exit "$rc"
          else
            echo "[check:pre-commit] llm-review failed (non-blocking); set GON_LLM_REVIEW_STRICT=1 to fail" >&2
          fi
        fi
      fi
    fi
    ;;

  report)
    out_html="${GON_REPORT_HTML:-tmp/proofpatch/status.html}"
    mkdir -p "$(dirname "$out_html")"

    echo "[check:report] building status report -> $out_html"

    if [[ -z "$PROOFPATCH_BIN" ]]; then
      echo "[check:report] proofpatch not available (install proofpatch or set PROOFPATCH_BIN)" >&2
      exit 2
    fi

    files=(
      "Covolume/Legendre/Main.lean"
      "Covolume/Legendre/Ankeny.lean"
      "Covolume/Cauchy/Main.lean"
    )

    "$PROOFPATCH_BIN" report --repo "$repo_root" --files "${files[@]}" \
      --timeout-s 120 --max-sorries 50 --context-lines 2 \
      --output-html "$out_html" || true

    echo "[check:report] wrote $out_html"
    ;;

  pre-push)
    echo "[check:pre-push] lake build"
    "$LAKE" build
    echo "[check:pre-push] lake lint"
    "$LAKE" lint
    echo "[check:pre-push] lint-style"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}"
    ;;

  ci)
    echo "[check:ci] lake build"
    "$LAKE" build
    echo "[check:ci] lake lint"
    "$LAKE" lint
    echo "[check:ci] lint-style"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}"
    ;;

  *)
    echo "usage: ./Scripts/check.sh {pre-commit|pre-push|ci|report} [--github]" >&2
    exit 2
    ;;
esac
