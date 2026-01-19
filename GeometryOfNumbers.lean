import Covolume

/-!
# Geometry of Numbers (facade)

This library is a **facade** over the existing `Covolume.*` modules.

Rationale:
- `Covolume` is the historical internal namespace.
- `GeometryOfNumbers` is the intended public-facing namespace and import root.

We intentionally avoid a mass rename/move of files (which is expensive and brittle in Lean),
and instead provide a stable surface via `export` declarations.
-/

namespace GeometryOfNumbers

/-!
## Facade policy

Lean does not have a robust “export everything from a namespace” command.
So we expose a **curated** set of names here, and grow it as the public API stabilizes.
-/

-- Core polygonal-number API (used by the Cauchy reduction).
abbrev polygonal := Covolume.polygonal
abbrev triangular := Covolume.triangular

-- Main theorem statements (these are the public entry points).
abbrev fermat_polygonal := Covolume.fermat_polygonal
abbrev gauss_triangular := Covolume.gauss_triangular

namespace Minkowski
  noncomputable abbrev E3 := Covolume.Minkowski.E3
  noncomputable abbrev ankenyDiagMap := Covolume.Minkowski.ankenyDiagMap
  noncomputable abbrev ankenyBallRadius := Covolume.Minkowski.ankenyBallRadius
  noncomputable abbrev ankenyEllipsoidAsPreimage := Covolume.Minkowski.ankenyEllipsoidAsPreimage
end Minkowski

end GeometryOfNumbers

