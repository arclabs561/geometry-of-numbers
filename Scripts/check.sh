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

source "$repo_root/Scripts/lib.sh"
resolve_lake

# Local artifacts (HTML + JSON) live under `tmp/proofpatch/` by default.
#
# Back-compat:
# - Older scripts/docs used `tmp/proofloops/`.
# - We still *read* legacy inputs from there if the new location is absent.
artifact_dir="${GON_ARTIFACT_DIR:-tmp/proofpatch}"
legacy_artifact_dir="tmp/proofloops"
mkdir -p "$artifact_dir"

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
      "$LAKE" build GeometryOfNumbers GeometryOfNumbers.Legendre.Main GeometryOfNumbers.Cauchy.Main

      # After a successful smoke build, emit a compact, structured summary of the current proof
      # frontier. This is primarily for humans/agents (so they don’t have to parse raw warnings).
      #
      # Opt out with `GON_PRECOMMIT_SUMMARY=0`.
      precommit_summary="${GON_PRECOMMIT_SUMMARY:-1}"
      if [[ "$precommit_summary" != "0" ]]; then
        echo "[check:pre-commit] proof frontier summary (proofpatch report)"
        if ! resolve_proof_cli; then
          echo "[check:pre-commit] proofpatch not available; skipping summary" >&2
        else
          out_html="${GON_PRECOMMIT_REPORT_HTML:-$artifact_dir/status.html}"
          files=(
            "GeometryOfNumbers/Legendre/Main.lean"
            "GeometryOfNumbers/Cauchy/Main.lean"
          )
          pp_run_fresh report --repo "$repo_root" --files "${files[@]}" --timeout-s 60 --max-sorries 50 --context-lines 1 \
            --output-html "$out_html"
        fi
      fi
    else
      echo "[check:pre-commit] lake build skipped (GON_PRECOMMIT_BUILD=0)" >&2
    fi
    echo "[check:pre-commit] lint-style (fast)"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}" --fast
    llm_on="${GON_LLM_REVIEW:-1}"
    if [[ "$llm_on" != "0" ]]; then
      echo "[check:pre-commit] llm-review (default on; set GON_LLM_REVIEW=0 to disable)"
      set +e
      # If strict, require an API key to be configured (so we don't silently skip).
      req=()
      strict="${GON_LLM_REVIEW_STRICT:-0}"
      if [[ "$strict" != "0" ]]; then
        req+=(--require-key)
      fi

      # Project-agnostic LLM diff review lives in `proofpatch` (Rust CLI).
      if ! resolve_proof_cli; then
        if [[ "$strict" != "0" ]]; then
          echo "[check:pre-commit] proofpatch not available (need ../proofpatch or proofpatch on PATH)" >&2
          exit 1
        else
          echo "[check:pre-commit] proofpatch not available; skipping llm-review" >&2
          set -e
          # Skip (non-blocking). Keep going with the rest of the profile.
          true
        fi
      fi

      if [[ "$PP_KIND" != "none" ]]; then
        # Keep pre-commit output readable: write full output to a local artifact and print a small JSON
        # “written” record to stdout.
        out_json="${GON_LLM_REVIEW_JSON:-$artifact_dir/review-diff.json}"
        out_prompt_json="${GON_LLM_REVIEW_PROMPT_JSON:-$artifact_dir/review-prompt.json}"
        review_scope="${GON_LLM_REVIEW_SCOPE:-auto}"
        # Bound the prompt pack so we don't exceed provider context limits.
        #
        # Keep these defaults *small* to avoid provider context overruns.
        # Override with env vars if you intentionally want a bigger prompt pack.
        max_total_bytes="${GON_LLM_REVIEW_MAX_TOTAL_BYTES:-40000}"
        per_file_bytes="${GON_LLM_REVIEW_PER_FILE_BYTES:-8000}"
        transcript_bytes="${GON_LLM_REVIEW_TRANSCRIPT_BYTES:-8000}"
      # Verification inside `proofpatch review-diff` reduces hallucinated “this file won’t build”
      # claims by providing a ground-truth `verify` summary for some `.lean` files.
      #
      # Keep the default bounded and fast; override if you want deeper coverage.
      verify_timeout_s="${GON_LLM_REVIEW_VERIFY_TIMEOUT_S:-20}"
      verify_max_files="${GON_LLM_REVIEW_VERIFY_MAX_FILES:-20}"

      # Also write the exact prompt pack used for review (diff+corpus+cache_key) for debugging.
      # This makes it easy to confirm whether a reviewer claim is actually present in the diff.
      #
      # Note: `review-prompt` uses the same scope resolver as `review-diff` when `--scope auto`.
      pp_run_fresh review-prompt --repo "$repo_root" --scope "$review_scope" \
        --max-total-bytes "$max_total_bytes" --per-file-bytes "$per_file_bytes" --transcript-bytes "$transcript_bytes" \
        --output-json "$out_prompt_json" >/dev/null 2>&1 || true

        if [[ "$PP_EXE" == "proofpatch" ]]; then
          pp_run_fresh review-diff --repo "$repo_root" --scope "$review_scope" \
          --verify-timeout-s "$verify_timeout_s" --verify-max-files "$verify_max_files" \
            --max-total-bytes "$max_total_bytes" --per-file-bytes "$per_file_bytes" --transcript-bytes "$transcript_bytes" \
            "${req[@]+"${req[@]}"}" --output-json "$out_json"
        else
          # Back-compat: older CLI may not support prompt-pack sizing flags.
          pp_run_fresh review-diff --repo "$repo_root" --scope "$review_scope" \
          --verify-timeout-s "$verify_timeout_s" --verify-max-files "$verify_max_files" \
            "${req[@]+"${req[@]}"}" --output-json "$out_json"
        fi

        rc=$?
        set -e
        if [[ -f "$out_json" ]] && command -v jq >/dev/null 2>&1; then
          echo "[check:pre-commit] llm-review summary"
          if jq -e '.skipped == true' "$out_json" >/dev/null 2>&1; then
            jq -r '"skipped=true\nreason=" + (.reason // "unknown")' "$out_json"
          else
            jq -r '"provider=" + (.provider // "unknown") + "\nmodel=" + (.model // "unknown") + "\nmodel_source=" + (.model_source // "unknown") + "\nmodel_env=" + (.model_env // "unknown") + "\nscope=" + (.scope_resolved // .scope // "unknown") + "\nselected_files=" + ((.selected_files|length)|tostring)' "$out_json"
            if jq -e '(.provider // "") == "openrouter" and ((.model_source // "") | test("^default"))' "$out_json" >/dev/null 2>&1; then
              echo "note=OPENROUTER_MODEL not set; using a conservative default. Consider choosing a stronger model via https://openrouter.ai/rankings"
            fi
            # Prefer structured output when available; otherwise print the full review text.
            if jq -e '.review_struct != null' "$out_json" >/dev/null 2>&1; then
              jq -r '"overall_score=" + (.review_struct.overall.score|tostring) + "\nverdict=" + (.review_struct.overall.verdict // "unknown") + "\nsummary=" + (.review_struct.overall.summary // "")' "$out_json"
              echo "axes:"
              jq -r '.review_struct.axes[0:6][]? | "- " + .name + " score=" + (.score|tostring) + " — " + (.summary // "")' "$out_json"
              echo "top_issues:"
              jq -r '.review_struct.top_issues[0:5][]? | "- [" + .severity + "] " + .title + (if (.files|length)>0 then " (" + (.files|join(", ")) + ")" else "" end)' "$out_json"
              echo "quick_wins:"
              jq -r '.review_struct.quick_wins[0:5][]? | "- " + .' "$out_json"
              verdict="$(jq -r '.review_struct.overall.verdict // "unknown"' "$out_json")"
              if [[ "$verdict" == "request_changes" ]]; then
                echo ""
                echo "[check:pre-commit] STOP: reviewer verdict=request_changes"
                echo "artifact=$out_json"
                if [[ -f "$out_prompt_json" ]]; then
                  echo "prompt_artifact=$out_prompt_json"
                  # Minimal sanity checks: do the prompt/diff actually contain the claimed strings?
                  # (This helps catch “stale diff” / hallucinations quickly.)
                  diff_has_covolume="$(jq -r '(.diff // "") | contains("Covolume")' "$out_prompt_json" 2>/dev/null || echo unknown)"
                  echo "sanity: diff_contains_Covolume=$diff_has_covolume"
                  if [[ "$diff_has_covolume" == "true" ]]; then
                    echo "hint=the staged diff really contains Covolume; likely you fixed it in the worktree but did not stage the fix"
                    echo "next=run: git diff --cached GeometryOfNumbers/Cauchy/MediumTablesMge22.lean"
                  elif [[ "$diff_has_covolume" == "false" ]]; then
                    echo "hint=the diff does NOT contain Covolume; treat any Covolume-based claim as likely hallucination/stale context"
                  fi
                fi
                # Another common failure mode: staged vs worktree mismatch.
                # If you have unstaged edits to files that are also staged, the staged review can
                # legitimately complain about issues you already fixed locally.
                if command -v git >/dev/null 2>&1; then
                  staged_list="$(git diff --cached --name-only --diff-filter=ACMRT || true)"
                  unstaged_list="$(git diff --name-only --diff-filter=ACMRT || true)"
                  if [[ -n "$staged_list" ]] && [[ -n "$unstaged_list" ]]; then
                    overlap="$(comm -12 <(printf "%s\n" "$staged_list" | sort -u) <(printf "%s\n" "$unstaged_list" | sort -u) || true)"
                    if [[ -n "$overlap" ]]; then
                      echo "warning=unstaged edits overlap staged files; reviewer saw staged version"
                      echo "$overlap" | sed 's/^/  - /'
                      echo "next=stage fixes (git add ...) then re-run just precommit"
                    fi
                  fi
                fi
                # Policy:
                # - default: warn loudly but do not fail the check
                # - strict: fail the check (prevents committing without addressing)
                # - override: allow failing even when strict=0
                fail_verdict="${GON_LLM_REVIEW_FAIL_VERDICT:-}"
                if [[ "$strict" != "0" ]] || [[ "$fail_verdict" == "request_changes" ]]; then
                  echo "[check:pre-commit] failing because verdict=request_changes" >&2
                  exit 3
                fi
              fi
            else
              echo "review_text:"
              # Print the review text inline so it is “in your face”; the JSON path remains the
              # canonical artifact.
              #
              # If this output is too verbose for your workflow, set:
              #   GON_LLM_REVIEW_PRINT=0
              print_review="${GON_LLM_REVIEW_PRINT:-1}"
              if [[ "$print_review" == "0" ]]; then
                echo "  (suppressed; set GON_LLM_REVIEW_PRINT=1 to print)"
                echo "  artifact=$out_json"
              else
                jq -r '.review_text // "(missing review_text; see artifact JSON)"' "$out_json"
              fi
            fi
          fi
        fi
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
    # Human-facing status snapshot (HTML artifact under tmp/).
    #
    # This is intentionally not part of CI: it writes a local artifact and is primarily for
    # interactive iteration.
    out_html="${GON_REPORT_HTML:-$artifact_dir/status.html}"
    mkdir -p "$(dirname "$out_html")"

    echo "[check:report] building status report -> $out_html"

    if ! resolve_proof_cli; then
      echo "[check:report] proofpatch not available (need ../proofpatch or proofpatch on PATH)" >&2
      exit 2
    fi

    # Curated list: high-signal proof frontiers.
    files=(
      "GeometryOfNumbers/Legendre/Main.lean"
      "GeometryOfNumbers/Legendre/Ankeny.lean"
      "GeometryOfNumbers/Legendre/Minkowski.lean"
      "GeometryOfNumbers/Cauchy/Main.lean"
      # Generated (or heavy) files: include them so the report can surface timeouts/warnings
      # as actionable “frontier” items.
      "GeometryOfNumbers/Cauchy/MediumTablesSmall.lean"
      "GeometryOfNumbers/Cauchy/MediumTablesMge22.lean"
      "GeometryOfNumbers/Core/SuccessiveMinima.lean"
      "GeometryOfNumbers/Core/SuccessiveMinimaTheorems.lean"
    )

    report_json="$artifact_dir/report.json"
    echo "[check:report] report json -> $report_json"
    pp_run_fresh report --repo "$repo_root" --files "${files[@]}" --timeout-s 120 --max-sorries 50 --context-lines 2 \
      --output-html "$out_html" > "$report_json"

    if command -v jq >/dev/null 2>&1; then
      echo "[check:report] frontier summary"
      jq -r '"next_actions=" + (.next_actions|length|tostring) + " files=" + (.table|length|tostring)' "$report_json"
    fi

    # Optional: ingest raw web-search JSON blobs into a small deduped notes file.
    #
    # Workflow:
    # - Put any MCP tool outputs you care about into:
    #     tmp/proofpatch/research/raw.json
    # - Then run:
    #     ./Scripts/check.sh report
    # - This will emit:
    #     tmp/proofpatch/research/research-notes.json
    #
    # This keeps `proofpatch` pure (it does not execute MCP calls), while making it easy to
    # fold external search results back into the local proof loop.
    raw_research="${GON_RESEARCH_RAW_JSON:-$artifact_dir/research/raw.json}"
    if [[ ! -f "$raw_research" ]] && [[ -f "$legacy_artifact_dir/research/raw.json" ]]; then
      raw_research="$legacy_artifact_dir/research/raw.json"
    fi
    if [[ -f "$raw_research" ]]; then
      research_notes="$artifact_dir/research/research-notes.json"
      echo "[check:report] research-ingest -> $research_notes"
      mkdir -p "$artifact_dir/research"
      pp_run_fresh research-ingest --input "$raw_research" --output-json "$research_notes"

      if command -v jq >/dev/null 2>&1; then
        echo "[check:report] research summary"
        jq -r '"raw_urls=" + (.raw_urls|tostring) + " deduped_urls=" + (.deduped_urls|tostring)' \
          "$research_notes"
        jq -r '.sources[0:10][] | "- " + .url + " (" + (.origin // "unknown") + ")"' \
          "$research_notes"

        out_enriched="$artifact_dir/report.enriched.json"
        echo "[check:report] attach research -> $out_enriched"
        pp_run_fresh research-attach --report-json "$report_json" --research-notes "$research_notes" \
          --top-k 3 --output-json "$out_enriched"
      else
        echo "[check:report] jq not found; skipping research-notes summary" >&2
      fi
    else
      echo "[check:report] no research JSON found at $raw_research (skipping)"
    fi

    # Also write “rubberduck” planning prompts as JSON for the main blockers.
    # (These are inputs to an agent/human loop, not proofs.)
    out_dir="$(dirname "$out_html")"
    set +e
    echo "[check:report] rubberduck prompts -> $out_dir"
    pp_run_fresh rubberduck-prompt --repo "$repo_root" --file "GeometryOfNumbers/Legendre/Main.lean" \
      --lemma "sum_three_squares_of_not_exception" \
      --output-json "$out_dir/rubberduck-legendre.json"
    pp_run_fresh rubberduck-prompt --repo "$repo_root" --file "GeometryOfNumbers/Cauchy/Main.lean" \
      --lemma "nathanson_parameters_large" \
      --output-json "$out_dir/rubberduck-nathanson.json"
    pp_run_fresh rubberduck-prompt --repo "$repo_root" --file "GeometryOfNumbers/Cauchy/Main.lean" \
      --lemma "cauchy_lemma" \
      --output-json "$out_dir/rubberduck-cauchy_lemma.json"
    rc=$?
    set -e
    if [[ $rc -ne 0 ]]; then
      echo "[check:report] warning: rubberduck prompt generation failed (non-blocking)" >&2
    fi

    # Optional: run an LLM pass over the rubberduck prompts (for faster math iteration).
    # Keep it opt-in: `GON_LLM_DUCK=1`.
    duck_on="${GON_LLM_DUCK:-0}"
    if [[ "$duck_on" != "0" ]]; then
      echo "[check:report] llm-chat over rubberduck prompts (GON_LLM_DUCK=1)"
      duck_system='You are a Lean 4/mathlib proof assistant. The user content is JSON from a proofpatch rubberduck-prompt. You MAY call a context-pack tool to fetch more context (imports/excerpt/nearby decls) instead of guessing. Return STRICT JSON (no markdown) with keys: goal, plan (array), lean_steps (array), math_notes (array), questions (array). Keep it minimal and actionable.'
      # Tool engine selector (defaults to the legacy loop).
      #
      # Values:
      # - agent       (typed agent loop; implementation detail may change)
      #
      # Back-compat: if someone sets `GON_LLM_DUCK_TOOLS=axi-proofloops`, treat it as `agent`.
      duck_tools="${GON_LLM_DUCK_TOOLS:-agent}"
      if [[ "$duck_tools" == "proofloops" ]]; then
        duck_tools="agent"
      fi
      if [[ "$duck_tools" == "axi-proofloops" ]]; then
        duck_tools="agent"
      fi
      echo "[check:report] duck tools: $duck_tools (set GON_LLM_DUCK_TOOLS=agent to use agent loop)"
      # Avoid mixing stale outputs from previous runs.
      rm -f "$out_dir"/duckreply-*.json
      set +e
      pp_run_fresh llm-chat --repo "$repo_root" --tools "$duck_tools" --system "$duck_system" --user-file "$out_dir/rubberduck-legendre.json" --timeout-s 120 \
        --output-json "$out_dir/duckreply-legendre.json"
      pp_run_fresh llm-chat --repo "$repo_root" --tools "$duck_tools" --system "$duck_system" --user-file "$out_dir/rubberduck-nathanson.json" --timeout-s 120 \
        --output-json "$out_dir/duckreply-nathanson.json"
      pp_run_fresh llm-chat --repo "$repo_root" --tools "$duck_tools" --system "$duck_system" --user-file "$out_dir/rubberduck-cauchy_lemma.json" --timeout-s 120 \
        --output-json "$out_dir/duckreply-cauchy_lemma.json"
      rc=$?
      set -e
      if [[ $rc -ne 0 ]]; then
        echo "[check:report] warning: llm-chat failed (non-blocking)" >&2
      elif command -v jq >/dev/null 2>&1; then
        echo "[check:report] duckreply summary"
        for f in "$out_dir"/duckreply-*.json; do
          if [[ -f "$f" ]]; then
            echo "- $(basename "$f")"
            if jq -e '.skipped == true' "$f" >/dev/null 2>&1; then
              jq -r '  "  skipped=true reason=" + (.reason // "unknown")' "$f"
            else
              jq -r '  "  provider=" + (.provider // "unknown") + " model=" + (.model // "unknown") + " (" + (.model_source // "unknown") + ")"' "$f"
              jq -r '  "  goal=" + ((.content_struct.goal // "unknown")|tostring)' "$f" 2>/dev/null || true
              if jq -e '(.provider // "") == "openrouter" and ((.model_source // "") | test("^default"))' "$f" >/dev/null 2>&1; then
                echo "  tip=set OPENROUTER_MODEL for better quality (see https://openrouter.ai/rankings)"
              fi
            fi
          fi
        done
      fi
    fi

    echo "[check:report] wrote $out_html"
    ;;
  pre-push)
    echo "[check:pre-push] lake build"
    "$LAKE" build
    echo "[check:pre-push] regen-check (generated tables audit)"
    # This is intentionally not part of pre-commit (too slow).
    # It MUST stay deterministic and should fail on drift.
    "$LAKE" --version >/dev/null 2>&1 || true
    uv run Scripts/regen_check_medium_tables.py
    echo "[check:pre-push] lake lint"
    "$LAKE" lint
    echo "[check:pre-push] lint-style"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}"
    ;;
  ci)
    # CI entrypoint: aim for “likely to pass CI”.
    #
    # In GitHub Actions, `lean-action` does the heavy setup, but we still want the same checks
    # to be runnable locally with a single command.
    echo "[check:ci] lake build"
    "$LAKE" build
    echo "[check:ci] regen-check (generated tables audit)"
    uv run Scripts/regen_check_medium_tables.py
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

