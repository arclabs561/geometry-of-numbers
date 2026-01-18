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
    echo "[check:pre-commit] covolume_checks"
    lake exe covolume_checks
    echo "[check:pre-commit] lint-style (fast)"
    ./Scripts/run_lint_style.sh "${lint_style_args[@]+"${lint_style_args[@]}"}" --fast
    if [[ "${COVOLUME_LLM_REVIEW:-1}" != "0" ]]; then
      echo "[check:pre-commit] llm-review (default on; set COVOLUME_LLM_REVIEW=0 to disable)"
      if command -v uv >/dev/null 2>&1; then
        set +e
        # If strict, require an API key to be configured (so we don't silently skip).
        req=()
        if [[ "${COVOLUME_LLM_REVIEW_STRICT:-0}" != "0" ]]; then
          req+=(--require-key)
        fi
        uv run Scripts/llm_review.py --scope staged "${req[@]+"${req[@]}"}"
        rc=$?
        set -e
        if [[ $rc -ne 0 ]]; then
          if [[ "${COVOLUME_LLM_REVIEW_STRICT:-0}" != "0" ]]; then
            exit "$rc"
          else
            echo "[check:pre-commit] llm-review failed (non-blocking); set COVOLUME_LLM_REVIEW_STRICT=1 to fail" >&2
          fi
        fi
      else
        echo "[check:pre-commit] uv not found; skipping llm-review" >&2
      fi
    fi
    ;;
  pre-push)
    echo "[check:pre-push] lake build"
    lake build
    echo "[check:pre-push] lake lint"
    lake lint
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

