import Mathlib.Algebra.Notation.Support

/-
# PNT port — `Function.support` patch

Verbatim port of `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` (Apache-2.0):
`support_id`/`support_id'` are not in our mathlib `v4.29.1` pin and are needed by the
`SmoothExistence` brick of the `weakPNT` discharge.
-/

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
