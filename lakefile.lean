import Lake
open Lake DSL

package «covolume» {
  -- Configure `lake lint` to run our project-owned checker.
  lintDriver := "covolume_checks"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "cced109deab25b4322e1a12b877335e092322b74"

@[default_target]
lean_lib «Covolume» {
  -- add library configuration options here
}

lean_lib «Experiments» {
  srcDir := "Experiments"
  -- Experiments policy: every file under `Experiments/` should compile under `lake build`.
  roots := #[
    `AnkenyCheck,
    `AnkenyL2Ellipsoid,
    `AnkenyReduction,
    `AnkenyVolumeConstants,
    `BhargavaCubes,
    `CauchyIntervals,
    `CheckMinkowski,
    `CheckNatPow,
    `CheckPiLpVolumePreserving,
    `CheckZMod,
    `DescentValuation,
    `FunBallToQ,
    `GramSchmidtCheck,
    `HenselLiftTwoSquares,
    `LLLBasic,
    `LLLRational,
    `SuccessiveMinimaBasic
  ]
}

lean_exe «status_report» {
  root := `Scripts.StatusReport
}

lean_exe «covolume_checks» {
  root := `Scripts.Checkers
}
