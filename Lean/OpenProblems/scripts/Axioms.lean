import OpenProblems

/-! Run `lake env lean scripts/Axioms.lean`: every main result must depend only on
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`). -/

open OpenProblems

#print axioms Hyperperfect.two_hyperperfect_characterization
#print axioms Hyperperfect.isHyperperfect_N
#print axioms Erdos318.erdos_318_contain_single_even
#print axioms Erdos939.erdos_939_six_infinite
#print axioms Erdos939.erdos_939_not_finite
#print axioms Erdos939.erdos_939_seven
#print axioms Erdos939.erdos_939_eight
#print axioms Ramsey.ramsey_three_three
#print axioms Ramsey.ramsey_three_four
#print axioms Ramsey.ramsey_three_five
#print axioms Ramsey.ramsey_four_four
#print axioms TriangleRamsey.multicolourTriangleRamsey_three
#print axioms WOWII91.conjecture91_false
#print axioms Thabit.thabit
#print axioms Proth.proth
#print axioms Lame.lame
#print axioms MirskyNewman.mirsky_newman
#print axioms Bondy.bondy
#print axioms Midy.midy
