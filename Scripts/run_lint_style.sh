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

# Prefer `proofyloops lint-style` (project-agnostic wrapper), but keep a self-contained fallback
# for environments where `uvx` isn't available (or proofyloops isn't reachable).
if command -v uvx >/dev/null 2>&1; then
  proofyloops_from=""
  if [[ -f "$repo_root/../proofyloops/pyproject.toml" ]]; then
    proofyloops_from="$repo_root/../proofyloops"
  else
    proofyloops_from="git+https://github.com/arclabs561/proofyloops"
  fi
  mod_args=()
  for m in "${modules[@]}"; do
    mod_args+=(--module "$m")
  done
  exec uvx --from "$proofyloops_from" proofyloops lint-style --repo "$repo_root" "${lint_args[@]+"${lint_args[@]}"}" "${mod_args[@]}"
fi

exec "$LAKE" exe lint-style "${lint_args[@]+"${lint_args[@]}"}" "${modules[@]}"

