import Lake
open Lake DSL

package «geometry_of_numbers» {
  -- Configure `lake lint` to run our project-owned checker.
  lintDriver := "gon_checks"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "cced109deab25b4322e1a12b877335e092322b74"

@[default_target]
lean_lib «Covolume» {
  -- add library configuration options here
}

/-!
`GeometryOfNumbers` is the **public facade** namespace.

Internally, most code still lives under `Covolume.*` (historical name), but new users should
prefer `import GeometryOfNumbers` and the `GeometryOfNumbers.*` modules.
-/
lean_lib «GeometryOfNumbers» {
  -- Facade: re-exports selected `Covolume` modules + curated API.
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

lean_exe «gon_checks» {
  root := `Scripts.Checkers
}

lean_exe «gon_precommit» {
  root := `Scripts.PreCommit
}
