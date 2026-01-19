import Covolume.Legendre.Ankeny

/-!
# Ankeny L2 ellipsoid volume (archived experiment)

This file previously implemented the L2-ball / `WithLp` volume normalization needed for the Ankeny
Minkowski step.

That work is now fully implemented in `Covolume/Legendre/Ankeny.lean`:

- `volume_ankenyEllipsoidL2_eq`
- `volume_ankenyEllipsoidL2_gt`

We keep this module as a lightweight pointer (no duplicate proofs, no `sorry`).
-/

namespace Covolume.Experiments

-- Intentionally no declarations: see `Covolume/Legendre/Ankeny.lean`.

end Covolume.Experiments
