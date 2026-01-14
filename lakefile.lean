import Lake
open Lake DSL

package «polygonal-number-theorem» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «PolygonalNumberTheorem» {
  -- add library configuration options here
}
