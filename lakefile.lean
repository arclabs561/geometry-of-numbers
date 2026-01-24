import Lake
open Lake DSL

package «geometry_of_numbers» {
  -- Configure `lake lint` to run our project-owned checker.
  lintDriver := "gon_checks"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "cced109deab25b4322e1a12b877335e092322b74"

@[default_target]
lean_lib «GeometryOfNumbers» {
  -- Public import root + public namespace.
}

/-!
`GeometryOfNumbers` is the public namespace and import root.
-/
-- (No additional `lean_lib` needed; already declared above.)

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
    `LegendreRemainingResidues,
    `LLLBasic,
    `LLLAnkenyBridge,
    `LLLRational,
    `SuccessiveMinimaBasic,
    `SuccessiveMinimaZ2,
    `PoissonTheta
  ]
}

lean_exe «status_report» {
  root := `Scripts.StatusReport
}

lean_exe «gon_checks» {
  root := `Scripts.Checkers
}

lean_exe «gon_precommit» {
  root := `Scripts.PreCommit
}

lean_exe «ankeny_check» {
  root := `Scripts.AnkenyCheck
}

lean_exe «lll_demo» {
  root := `Scripts.LLLDemo
}
