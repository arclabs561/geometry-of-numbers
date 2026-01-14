import PolygonalNumberTheorem.SumThreeSquares
import PolygonalNumberTheorem.MinkowskiDescent

def main : IO Unit := do
  IO.println "Polygonal Number Theorem Project Status:"
  IO.println "----------------------------------------"
  IO.println "1. Easy Direction (n = sum 3 sq => n != 4^a(8k+7)): PROVEN"
  IO.println "2. Square-Free Reduction: PROVEN"
  IO.println "3. Ankeny Prime Existence: PROVEN (via Dirichlet)"
  IO.println "4. Minkowski Lattice Definition: DEFINED"
  IO.println "----------------------------------------"
  IO.println "Next Steps:"
  IO.println " - Finish Ankeny algebraic descent OR"
  IO.println " - Calculate determinant of Minkowski lattice"
