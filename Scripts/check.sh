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

      # Project-agnostic LLM diff review lives in the helper repo `proofloops` (Rust CLI).
      # If no provider is configured, skip (or fail in strict mode) early to avoid
      # doing a `cargo run` that can stall on locks.
      has_provider=0
      if [[ -n "${OLLAMA_MODEL:-}" ]] || [[ -n "${GROQ_API_KEY:-}" ]] || [[ -n "${OPENAI_API_KEY:-}" ]] || [[ -n "${OPENROUTER_API_KEY:-}" ]]; then
        has_provider=1
      fi
      do_llm=1
      if [[ "$has_provider" -eq 0 ]]; then
        if [[ "$strict" != "0" ]]; then
          echo "[check:pre-commit] llm-review enabled but no provider configured" >&2
          echo "Set one of: OLLAMA_MODEL | GROQ_API_KEY | OPENAI_API_KEY | OPENROUTER_API_KEY" >&2
          exit 1
        else
          echo "[check:pre-commit] llm-review skipped (no provider configured)" >&2
          do_llm=0
        fi
      fi

      if [[ "$do_llm" -eq 0 ]]; then
        set -e
        true
      else
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
        if [[ "$pl_bin" == "cargo" ]]; then
          cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
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

