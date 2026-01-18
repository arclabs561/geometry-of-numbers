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

exec lake exe lint-style "${lint_args[@]+"${lint_args[@]}"}" "${modules[@]}"

