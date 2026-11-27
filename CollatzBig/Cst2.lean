import Collatz.CoeffStopDefs

/-! Kernel check: every `2 ≤ n` in this range drops below itself at its coefficient stopping time. -/

theorem CollatzBig.cst2 : Collatz.kallFrom (Collatz.cstCheck 1000) 65536 32768 = true := by
  decide +kernel
