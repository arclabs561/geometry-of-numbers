import Covolume.Legendre.Ankeny

/-!
# Fun detour: ball preimage → weighted sum of squares

This file used to hold a standalone lemma converting an ellipsoid-as-preimage-of-ball membership
into an explicit weighted quadratic-inequality.

That conversion is now implemented directly in `Covolume/Legendre/Ankeny.lean` in the strict-bound
step (search for the block that derives `hsum_sq_lt` from `hp_diag_mem`).
-/
-- Intentionally no declarations: this module is now a pointer to the canonical proof.
