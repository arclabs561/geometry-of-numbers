#!/usr/bin/env bash
set -euo pipefail

# Run `lake exe lint-style` with the repo's canonical module list.
#
# Usage:
#   ./Scripts/run_lint_style.sh [--github] [--fast]
#
# - `--github`: emit GitHub problem-matcher-friendly output
# - `--fast`: lint only `Covolume` (skip Experiments)

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

github=0
fast=0
for arg in "$@"; do
  case "$arg" in
    --github) github=1 ;;
    --fast) fast=1 ;;
    *) ;;
  esac
done

lint_args=()
if [[ "$github" -eq 1 ]]; then
  lint_args+=(--github)
fi

modules=(Covolume)
if [[ "$fast" -eq 0 ]]; then
  modules+=(
    Experiments.AnkenyCheck
    Experiments.AnkenyL2Ellipsoid
    Experiments.LLLBasic
    Experiments.CauchyIntervals
    Experiments.AnkenyReduction
    Experiments.AnkenyVolumeConstants
    Experiments.CheckMinkowski
    Experiments.CheckNatPow
    Experiments.CheckPiLpVolumePreserving
    Experiments.CheckZMod
    Experiments.DescentValuation
    Experiments.SuccessiveMinimaBasic
    Experiments.BhargavaCubes
    Experiments.FunBallToQ
    Experiments.LLLRational
    Experiments.GramSchmidtCheck
    Experiments.HenselLiftTwoSquares
  )
fi

# Prefer `proofloops lint-style` (project-agnostic Rust CLI), but keep a self-contained fallback
# for environments where proofloops isn't available.
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

if [[ -n "$pl_bin" ]]; then
  mod_args=()
  for m in "${modules[@]}"; do
    mod_args+=(--module "$m")
  done
  if [[ "$pl_bin" == "cargo" ]]; then
    exec cargo run --manifest-path "$pl_root/proofloops-core/Cargo.toml" --bin proofloops -- \
      lint-style --repo "$repo_root" "${lint_args[@]+"${lint_args[@]}"}" "${mod_args[@]}"
  fi
  exec "$pl_bin" lint-style --repo "$repo_root" "${lint_args[@]+"${lint_args[@]}"}" "${mod_args[@]}"
fi

exec "$LAKE" exe lint-style "${lint_args[@]+"${lint_args[@]}"}" "${modules[@]}"

