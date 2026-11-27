import Collatz.CoeffStopDefs

/-! Kernel check: every `2 ≤ n` in this range drops below itself at its coefficient stopping time. -/

theorem CollatzBig.cst0 : Collatz.kallFrom (Collatz.cstCheck 1000) 0 32768 = true := by
  decide +kernel
