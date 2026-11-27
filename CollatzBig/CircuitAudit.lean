import CollatzBig.Circuit

/-! Axiom check for the bounded circuit theorem (compiled by `scripts/assemble_ext.sh`). -/

/-- info: 'CollatzBig.Circuit.no_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.Circuit.no_circuit

/-- info: 'CollatzBig.Circuit.reachesOne_of_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms CollatzBig.Circuit.reachesOne_of_circuit
