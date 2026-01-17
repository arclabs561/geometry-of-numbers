import Lake
open Lake DSL

package «covolume» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "cced109deab25b4322e1a12b877335e092322b74"

@[default_target]
lean_lib «Covolume» {
  -- add library configuration options here
}

lean_lib «Experiments» {
  srcDir := "Experiments"
  roots := #[`AnkenyCheck, `LLLBasic, `CauchyIntervals, `AnkenyReduction, `CheckMinkowski, `CheckNatPow, `CheckZMod, `DescentValuation, `SuccessiveMinimaBasic, `BhargavaCubes]
}

lean_lib «Archive» {
  srcDir := "Archive"
}

lean_exe «status_report» {
  root := `Scripts.StatusReport
}
