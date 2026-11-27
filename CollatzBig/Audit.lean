import CollatzBig.Bridge

/-! Axiom check for the 2^32 results (compiled by `scripts/assemble_big.sh`). -/

/-- info: 'CollatzBig.descends_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.descends_below

/-- info: 'CollatzBig.cycle_length_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.cycle_length_ge

/-- info: 'CollatzBig.kstepT_period_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.kstepT_period_ge

/-- info: 'CollatzBig.natCast_periodic_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.natCast_periodic_ge
