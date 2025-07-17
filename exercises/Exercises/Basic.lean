import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by
  calc
  a = 2 * b + 5 := by rw[h1]
   _= 2 * 3 + 5 := by rw[h2]
   _=11 := by ring
