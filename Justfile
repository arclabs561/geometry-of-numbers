default: fast

# Geometry-of-numbers local “north star”:
# - keep a cheap, fast feedback loop
# - keep the slow/full build available when you intend it

lake_bin := env_var_or_default("LAKE", env_var("HOME") + "/.elan/bin/lake")

# Fast lane: core Legendre proof path + scripts + a couple key experiments.
fast:
    {{lake_bin}} build GeometryOfNumbers.Legendre.Main
    {{lake_bin}} build GeometryOfNumbers.Legendre.Ankeny
    {{lake_bin}} build Scripts.StatusReport
    {{lake_bin}} build Scripts.AnkenyCheck
    {{lake_bin}} build CheckMinkowski

status:
    {{lake_bin}} exe status_report

ankeny:
    {{lake_bin}} exe ankeny_check

checks:
    {{lake_bin}} exe gon_checks

# Deterministic regen/audit check for generated tables.
regen-check:
    uv run Scripts/regen_check_medium_tables.py

# Run the canonical repo check profiles (includes proofpatch integration when available).
precommit:
    ./Scripts/check.sh pre-commit

prepush:
    ./Scripts/check.sh pre-push

report:
    ./Scripts/check.sh report

# Build all experiment roots explicitly (keeps them compiling without the full build).
experiments:
    {{lake_bin}} build AnkenyCheck
    {{lake_bin}} build AnkenyL2Ellipsoid
    {{lake_bin}} build AnkenyReduction
    {{lake_bin}} build AnkenyVolumeConstants
    {{lake_bin}} build BhargavaCubes
    {{lake_bin}} build CauchyIntervals
    {{lake_bin}} build CheckMinkowski
    {{lake_bin}} build CheckNatPow
    {{lake_bin}} build CheckPiLpVolumePreserving
    {{lake_bin}} build CheckZMod
    {{lake_bin}} build DescentValuation
    {{lake_bin}} build FunBallToQ
    {{lake_bin}} build GramSchmidtCheck
    {{lake_bin}} build HenselLiftTwoSquares
    {{lake_bin}} build LegendreRemainingResidues
    {{lake_bin}} build LLLBasic
    {{lake_bin}} build LLLRational
    {{lake_bin}} build SuccessiveMinimaBasic
    {{lake_bin}} build SuccessiveMinimaZ2
    {{lake_bin}} build PoissonTheta

# Slow lane: full build (includes big tables).
all:
    {{lake_bin}} build

