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

      # Project-agnostic LLM diff review lives in the helper repo `proofyloops` (Rust CLI).
      pl_bin=""
      if [[ -x "$repo_root/../proofyloops/proofyloops-core/target/release/proofyloops" ]]; then
        pl_bin="$repo_root/../proofyloops/proofyloops-core/target/release/proofyloops"
      elif [[ -f "$repo_root/../proofyloops/proofyloops-core/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
        pl_bin="cargo"
      elif command -v proofyloops >/dev/null 2>&1; then
        pl_bin="proofyloops"
      fi

      if [[ -z "$pl_bin" ]]; then
        if [[ "$strict" != "0" ]]; then
          echo "[check:pre-commit] proofyloops not available (need ../proofyloops or proofyloops on PATH)" >&2
          exit 1
        else
          echo "[check:pre-commit] proofyloops not available; skipping llm-review" >&2
          set -e
          # Skip (non-blocking). Keep going with the rest of the profile.
          true
        fi
      fi

      if [[ -n "$pl_bin" ]]; then
        if [[ "$pl_bin" == "cargo" ]]; then
          cargo run --manifest-path "$repo_root/../proofyloops/proofyloops-core/Cargo.toml" --bin proofyloops -- \
            review-diff --repo "$repo_root" --scope staged "${req[@]+"${req[@]}"}"
        else
          "$pl_bin" review-diff --repo "$repo_root" --scope staged "${req[@]+"${req[@]}"}"
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
  pre-push)
    echo "[check:pre-push] lake build"
    "$LAKE" build
    echo "[check:pre-push] lake lint"
    "$LAKE" lint
    echo "[check:pre-push] lint-style"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}"
    ;;
  ci)
    # CI already runs `lean-action` + docgen; we keep this as a small, explicit check step.
    echo "[check:ci] lint-style"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}"
    ;;
  *)
    echo "usage: ./Scripts/check.sh {pre-commit|pre-push|ci} [--github]" >&2
    exit 2
    ;;
esac

