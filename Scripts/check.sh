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
    else
      echo "[check:pre-commit] lake build skipped (GON_PRECOMMIT_BUILD=0)" >&2
    fi
    echo "[check:pre-commit] lint-style (fast)"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}" --fast
    llm_on="${GON_LLM_REVIEW:-${COVOLUME_LLM_REVIEW:-1}}"
    if [[ "$llm_on" != "0" ]]; then
      echo "[check:pre-commit] llm-review (default on; set GON_LLM_REVIEW=0 to disable)"
      set +e
      # If strict, require an API key to be configured (so we don't silently skip).
      req=()
      strict="${GON_LLM_REVIEW_STRICT:-${COVOLUME_LLM_REVIEW_STRICT:-0}}"
      if [[ "$strict" != "0" ]]; then
        req+=(--require-key)
      fi

      # Project-agnostic LLM diff review lives in the helper repo `proofloops` (Rust CLI).
      pl_bin=""
      # Prefer a sibling checkout (../proofloops). Fall back to PATH.
      pl_root=""
      if [[ -d "$repo_root/../proofloops" ]]; then
        pl_root="$repo_root/../proofloops"
      fi

      if [[ -n "$pl_root" ]] && [[ -x "$pl_root/target/release/proofloops" ]]; then
        pl_bin="$pl_root/target/release/proofloops"
      elif [[ -n "$pl_root" ]] && [[ -x "$pl_root/target/debug/proofloops" ]]; then
        pl_bin="$pl_root/target/debug/proofloops"
      elif [[ -n "$pl_root" ]] && [[ -x "$pl_root/proofloops-core/target/release/proofloops" ]]; then
        # Legacy-ish path.
        pl_bin="$pl_root/proofloops-core/target/release/proofloops"
      elif [[ -n "$pl_root" ]] && [[ -x "$pl_root/proofloops-core/target/debug/proofloops" ]]; then
        # Legacy-ish path.
        pl_bin="$pl_root/proofloops-core/target/debug/proofloops"
      elif [[ -n "$pl_root" ]] && [[ -f "$pl_root/proofloops-core/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
        pl_bin="cargo"
      elif command -v proofloops >/dev/null 2>&1; then
        pl_bin="proofloops"
      fi

      if [[ -z "$pl_bin" ]]; then
        if [[ "$strict" != "0" ]]; then
          echo "[check:pre-commit] proofloops not available (need ../proofloops or proofloops on PATH)" >&2
          exit 1
        else
          echo "[check:pre-commit] proofloops not available; skipping llm-review" >&2
          set -e
          # Skip (non-blocking). Keep going with the rest of the profile.
          true
        fi
      fi

      if [[ -n "$pl_bin" ]]; then
        # Keep pre-commit output readable: write full output to a local artifact and print a small JSON
        # “written” record to stdout.
        mkdir -p tmp/proofloops
        out_json="${GON_LLM_REVIEW_JSON:-tmp/proofloops/review-diff.json}"
        if [[ "$pl_bin" == "cargo" ]]; then
          cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
            review-diff --repo "$repo_root" --scope staged "${req[@]+"${req[@]}"}" --output-json "$out_json"
        else
          "$pl_bin" review-diff --repo "$repo_root" --scope staged "${req[@]+"${req[@]}"}" --output-json "$out_json"
        fi

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
    # Human-facing status snapshot (HTML artifact under tmp/).
    #
    # This is intentionally not part of CI: it writes a local artifact and is primarily for
    # interactive iteration.
    out_html="${GON_REPORT_HTML:-tmp/proofloops/status.html}"
    mkdir -p "$(dirname "$out_html")"

    echo "[check:report] building status report -> $out_html"

    # Prefer a sibling checkout (../proofloops). Fall back to PATH; last resort is `cargo run`.
    pl_bin=""
    pl_root=""
    if [[ -d "$repo_root/../proofloops" ]]; then
      pl_root="$repo_root/../proofloops"
    fi

    if [[ -n "$pl_root" ]] && [[ -x "$pl_root/target/release/proofloops" ]]; then
      pl_bin="$pl_root/target/release/proofloops"
    elif [[ -n "$pl_root" ]] && [[ -x "$pl_root/target/debug/proofloops" ]]; then
      pl_bin="$pl_root/target/debug/proofloops"
    elif command -v proofloops >/dev/null 2>&1; then
      pl_bin="proofloops"
    elif [[ -n "$pl_root" ]] && [[ -f "$pl_root/proofloops-core/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
      pl_bin="cargo"
    fi

    if [[ -z "$pl_bin" ]]; then
      echo "[check:report] proofloops not available (need ../proofloops or proofloops on PATH)" >&2
      exit 2
    fi

    # Curated list: high-signal proof frontiers.
    files=(
      "Covolume/Legendre/Main.lean"
      "Covolume/Legendre/Ankeny.lean"
      "Covolume/Cauchy/Main.lean"
    )

    if [[ "$pl_bin" == "cargo" ]]; then
      cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
        report --repo "$repo_root" --files "${files[@]}" --timeout-s 120 --max-sorries 50 --context-lines 2 \
        --output-html "$out_html"
    else
      "$pl_bin" report --repo "$repo_root" --files "${files[@]}" --timeout-s 120 --max-sorries 50 --context-lines 2 \
        --output-html "$out_html"
    fi

    # Also write “rubberduck” planning prompts as JSON for the main blockers.
    # (These are inputs to an agent/human loop, not proofs.)
    out_dir="$(dirname "$out_html")"
    set +e
    echo "[check:report] rubberduck prompts -> $out_dir"
    if [[ "$pl_bin" == "cargo" ]]; then
      cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
        rubberduck-prompt --repo "$repo_root" --file "Covolume/Legendre/Main.lean" \
        --lemma "sum_three_squares_of_not_exception" \
        --output-json "$out_dir/rubberduck-legendre.json"
      cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
        rubberduck-prompt --repo "$repo_root" --file "Covolume/Cauchy/Main.lean" \
        --lemma "nathanson_parameters" \
        --output-json "$out_dir/rubberduck-nathanson.json"
      cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
        rubberduck-prompt --repo "$repo_root" --file "Covolume/Cauchy/Main.lean" \
        --lemma "cauchy_lemma" \
        --output-json "$out_dir/rubberduck-cauchy_lemma.json"
    else
      "$pl_bin" rubberduck-prompt --repo "$repo_root" --file "Covolume/Legendre/Main.lean" \
        --lemma "sum_three_squares_of_not_exception" \
        --output-json "$out_dir/rubberduck-legendre.json"
      "$pl_bin" rubberduck-prompt --repo "$repo_root" --file "Covolume/Cauchy/Main.lean" \
        --lemma "nathanson_parameters" \
        --output-json "$out_dir/rubberduck-nathanson.json"
      "$pl_bin" rubberduck-prompt --repo "$repo_root" --file "Covolume/Cauchy/Main.lean" \
        --lemma "cauchy_lemma" \
        --output-json "$out_dir/rubberduck-cauchy_lemma.json"
    fi
    rc=$?
    set -e
    if [[ $rc -ne 0 ]]; then
      echo "[check:report] warning: rubberduck prompt generation failed (non-blocking)" >&2
    fi

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
    # CI entrypoint: aim for “likely to pass CI”.
    #
    # In GitHub Actions, `lean-action` does the heavy setup, but we still want the same checks
    # to be runnable locally with a single command.
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

