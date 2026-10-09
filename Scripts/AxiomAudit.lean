import GeometryOfNumbers
import GeometryOfNumbers.Computable.LLLExactTermination

/-!
Axiom audit for the headline theorems (the README's verification boundary).

`#guard_msgs` fails `lake env lean Scripts/AxiomAudit.lean` if any of these
starts depending on another axiom, such as `sorryAx` or a new `native_decide`
certificate. Regenerate the expected lists with `#print axioms` when a change is
intended.
-/

/-- info: 'GeometryOfNumbers.sum_three_squares_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometryOfNumbers.sum_three_squares_iff

/-- info: 'GeometryOfNumbers.gauss_triangular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometryOfNumbers.gauss_triangular

/-- info: 'GeometryOfNumbers.fermat_polygonal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 GeometryOfNumbers.cauchyMediumSmall_s10_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s11_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s12_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s13_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s14_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s15_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s16_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s17_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s18_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s19_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s20_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s21_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s22_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s23_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s5_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s6_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s7_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s8_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumSmall_s9_spec._native.native_decide.ax_1_1,
 GeometryOfNumbers.cauchyMediumDefault_spec._native.native_decide.ax_1_1✝,
 GeometryOfNumbers.cauchyMediumSpecial_spec._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometryOfNumbers.fermat_polygonal

/-- info: 'GeometryOfNumbers.Computable.lllRunExact_finished_of_RowLIQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GeometryOfNumbers.Computable.lllRunExact_finished_of_RowLIQ
