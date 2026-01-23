import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even

/-!
Brute-checks for the Nathanson/Cauchy inequality window.

This file is **not** a proof. It's a small executable sanity check to guide the remaining
`nathanson_parameters` lemma in `GeometryOfNumbers/Cauchy/Main.lean`.

Given `s ≥ 5` and `n`, we attempt to find `b q r` such that:

- `Odd b`
- `0 ≤ r ≤ (s-2) - 2 = s-4`
- `n = (s-2) * q + b + r`
- with `a := 2*q + b`, the Cauchy window inequalities hold:
  \(b^2 < 4a\) and \(3a < b^2 + 2b + 4\).

If this experiment consistently fails for some small range, it's a strong signal that our
formal statement is missing a hypothesis (e.g. `n` large enough) or the choice strategy for `b`
needs adjustment.
-/

namespace GeometryOfNumbers.Experiments

private def m (s : Nat) : Nat := s - 2

private def isOddNat (b : Nat) : Bool :=
  b % 2 == 1

private def window_ok (b q : Nat) : Bool :=
  let a : Nat := 2 * q + b
  let bi : Int := Int.ofNat b
  let ai : Int := Int.ofNat a
  let b2 : Int := bi * bi
  (b2 < 4 * ai) && (3 * ai < b2 + 2 * bi + 4)

private def choose_qr (s n b : Nat) : Option (Nat × Nat) :=
  let mm := m s
  if mm < 3 then
    none
  else if b > n then
    none
  else
    -- r := (n-b) % m, but avoid the last residue class m-1 by shifting b -> b+2 if needed.
    let x := n - b
    let r0 := x % mm
    if r0 == mm - 1 then
      if b + 2 ≤ n then
        let b' := b + 2
        let x' := n - b'
        let r := x' % mm
        let q := (n - b' - r) / mm
        some (q, r)
      else
        none
    else
      let r := r0
      let q := (n - b - r) / mm
      some (q, r)

private partial def search_b (s n b : Nat) : Option (Nat × Nat × Nat) :=
  if b > n then
    none
  else if isOddNat b then
    match choose_qr s n b with
    | none => search_b s n (b + 1)
    | some (q, r) =>
        if r ≤ s - 4 && window_ok b q then
          some (b, q, r)
        else
          search_b s n (b + 1)
  else
    search_b s n (b + 1)

def find_window (s n : Nat) : Option (Nat × Nat × Nat) :=
  search_b s n 1

-- Small spot checks (kept as *definitions*, not executed during builds).
def sample_window_5_100 : Option (Nat × Nat × Nat) := find_window 5 100
def sample_window_6_200 : Option (Nat × Nat × Nat) := find_window 6 200

end GeometryOfNumbers.Experiments

