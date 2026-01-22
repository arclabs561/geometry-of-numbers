#!/usr/bin/env bash
set -euo pipefail

# Run `lake exe lint-style` with the repo's canonical module list.
#
# Usage:
#   ./Scripts/run_lint_style.sh [--github] [--fast]
#
# - `--github`: emit GitHub problem-matcher-friendly output
# - `--fast`: lint only `GeometryOfNumbers` (skip Experiments)

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

source "$repo_root/Scripts/lib.sh"
resolve_lake

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

modules=(GeometryOfNumbers)
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

if resolve_proof_cli; then
  mod_args=()
  for m in "${modules[@]}"; do
    mod_args+=(--module "$m")
  done
  pp_run lint-style --repo "$repo_root" "${lint_args[@]+"${lint_args[@]}"}" "${mod_args[@]}"
  exit $?
fi

exec "$LAKE" exe lint-style "${lint_args[@]+"${lint_args[@]}"}" "${modules[@]}"

