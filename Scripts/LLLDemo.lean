import GeometryOfNumbers.Computable.LLLExact

open GeometryOfNumbers.Computable

def rowList {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : List ℤ :=
  List.ofFn (fun j : Fin n => B i j)

def showBasis {n : ℕ} (label : String) (B : Matrix (Fin n) (Fin n) ℤ) : IO Unit := do
  IO.println s!"{label}:"
  for i in (List.ofFn (fun i : Fin n => i)) do
    IO.println s!"  {rowList B i}"

def demo3 : IO Unit := do
  -- Keep this tiny: the exact (ℚ) Gram–Schmidt path is correct but not optimized yet.
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]
  let δ : ℚ := (3 : ℚ) / 4
  let Bout := lllReduceExact (n := 2) B δ (limit := 50)
  showBasis "input" B
  showBasis "lll_exact output" Bout

def main : IO Unit := demo3
