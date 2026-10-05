/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.E1CertCore

/-! Kernel table for `E1Cert.cert_all`: `t = 1`, `a ∈ [9, 18)`. -/

namespace E1Cert.Table

set_option maxRecDepth 100000

theorem L1_9_0 : ∀ c : Fin 27, Fast.CertV ![9, 0, c] 1 := by decide +kernel

theorem L1_9_1 : ∀ c : Fin 27, Fast.CertV ![9, 1, c] 1 := by decide +kernel

theorem L1_9_2 : ∀ c : Fin 27, Fast.CertV ![9, 2, c] 1 := by decide +kernel

theorem L1_9_3 : ∀ c : Fin 27, Fast.CertV ![9, 3, c] 1 := by decide +kernel

theorem L1_9_4 : ∀ c : Fin 27, Fast.CertV ![9, 4, c] 1 := by decide +kernel

theorem L1_9_5 : ∀ c : Fin 27, Fast.CertV ![9, 5, c] 1 := by decide +kernel

theorem L1_9_6 : ∀ c : Fin 27, Fast.CertV ![9, 6, c] 1 := by decide +kernel

theorem L1_9_7 : ∀ c : Fin 27, Fast.CertV ![9, 7, c] 1 := by decide +kernel

theorem L1_9_8 : ∀ c : Fin 27, Fast.CertV ![9, 8, c] 1 := by decide +kernel

theorem L1_9_9 : ∀ c : Fin 27, Fast.CertV ![9, 9, c] 1 := by decide +kernel

theorem L1_9_10 : ∀ c : Fin 27, Fast.CertV ![9, 10, c] 1 := by decide +kernel

theorem L1_9_11 : ∀ c : Fin 27, Fast.CertV ![9, 11, c] 1 := by decide +kernel

theorem L1_9_12 : ∀ c : Fin 27, Fast.CertV ![9, 12, c] 1 := by decide +kernel

theorem L1_9_13 : ∀ c : Fin 27, Fast.CertV ![9, 13, c] 1 := by decide +kernel

theorem L1_9_14 : ∀ c : Fin 27, Fast.CertV ![9, 14, c] 1 := by decide +kernel

theorem L1_9_15 : ∀ c : Fin 27, Fast.CertV ![9, 15, c] 1 := by decide +kernel

theorem L1_9_16 : ∀ c : Fin 27, Fast.CertV ![9, 16, c] 1 := by decide +kernel

theorem L1_9_17 : ∀ c : Fin 27, Fast.CertV ![9, 17, c] 1 := by decide +kernel

theorem L1_9_18 : ∀ c : Fin 27, Fast.CertV ![9, 18, c] 1 := by decide +kernel

theorem L1_9_19 : ∀ c : Fin 27, Fast.CertV ![9, 19, c] 1 := by decide +kernel

theorem L1_9_20 : ∀ c : Fin 27, Fast.CertV ![9, 20, c] 1 := by decide +kernel

theorem L1_9_21 : ∀ c : Fin 27, Fast.CertV ![9, 21, c] 1 := by decide +kernel

theorem L1_9_22 : ∀ c : Fin 27, Fast.CertV ![9, 22, c] 1 := by decide +kernel

theorem L1_9_23 : ∀ c : Fin 27, Fast.CertV ![9, 23, c] 1 := by decide +kernel

theorem L1_9_24 : ∀ c : Fin 27, Fast.CertV ![9, 24, c] 1 := by decide +kernel

theorem L1_9_25 : ∀ c : Fin 27, Fast.CertV ![9, 25, c] 1 := by decide +kernel

theorem L1_9_26 : ∀ c : Fin 27, Fast.CertV ![9, 26, c] 1 := by decide +kernel

theorem A1_9 : ∀ b c : Fin 27, Fast.CertV ![9, b, c] 1
  | ⟨0, _⟩ => L1_9_0
  | ⟨1, _⟩ => L1_9_1
  | ⟨2, _⟩ => L1_9_2
  | ⟨3, _⟩ => L1_9_3
  | ⟨4, _⟩ => L1_9_4
  | ⟨5, _⟩ => L1_9_5
  | ⟨6, _⟩ => L1_9_6
  | ⟨7, _⟩ => L1_9_7
  | ⟨8, _⟩ => L1_9_8
  | ⟨9, _⟩ => L1_9_9
  | ⟨10, _⟩ => L1_9_10
  | ⟨11, _⟩ => L1_9_11
  | ⟨12, _⟩ => L1_9_12
  | ⟨13, _⟩ => L1_9_13
  | ⟨14, _⟩ => L1_9_14
  | ⟨15, _⟩ => L1_9_15
  | ⟨16, _⟩ => L1_9_16
  | ⟨17, _⟩ => L1_9_17
  | ⟨18, _⟩ => L1_9_18
  | ⟨19, _⟩ => L1_9_19
  | ⟨20, _⟩ => L1_9_20
  | ⟨21, _⟩ => L1_9_21
  | ⟨22, _⟩ => L1_9_22
  | ⟨23, _⟩ => L1_9_23
  | ⟨24, _⟩ => L1_9_24
  | ⟨25, _⟩ => L1_9_25
  | ⟨26, _⟩ => L1_9_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_10_0 : ∀ c : Fin 27, Fast.CertV ![10, 0, c] 1 := by decide +kernel

theorem L1_10_1 : ∀ c : Fin 27, Fast.CertV ![10, 1, c] 1 := by decide +kernel

theorem L1_10_2 : ∀ c : Fin 27, Fast.CertV ![10, 2, c] 1 := by decide +kernel

theorem L1_10_3 : ∀ c : Fin 27, Fast.CertV ![10, 3, c] 1 := by decide +kernel

theorem L1_10_4 : ∀ c : Fin 27, Fast.CertV ![10, 4, c] 1 := by decide +kernel

theorem L1_10_5 : ∀ c : Fin 27, Fast.CertV ![10, 5, c] 1 := by decide +kernel

theorem L1_10_6 : ∀ c : Fin 27, Fast.CertV ![10, 6, c] 1 := by decide +kernel

theorem L1_10_7 : ∀ c : Fin 27, Fast.CertV ![10, 7, c] 1 := by decide +kernel

theorem L1_10_8 : ∀ c : Fin 27, Fast.CertV ![10, 8, c] 1 := by decide +kernel

theorem L1_10_9 : ∀ c : Fin 27, Fast.CertV ![10, 9, c] 1 := by decide +kernel

theorem L1_10_10 : ∀ c : Fin 27, Fast.CertV ![10, 10, c] 1 := by decide +kernel

theorem L1_10_11 : ∀ c : Fin 27, Fast.CertV ![10, 11, c] 1 := by decide +kernel

theorem L1_10_12 : ∀ c : Fin 27, Fast.CertV ![10, 12, c] 1 := by decide +kernel

theorem L1_10_13 : ∀ c : Fin 27, Fast.CertV ![10, 13, c] 1 := by decide +kernel

theorem L1_10_14 : ∀ c : Fin 27, Fast.CertV ![10, 14, c] 1 := by decide +kernel

theorem L1_10_15 : ∀ c : Fin 27, Fast.CertV ![10, 15, c] 1 := by decide +kernel

theorem L1_10_16 : ∀ c : Fin 27, Fast.CertV ![10, 16, c] 1 := by decide +kernel

theorem L1_10_17 : ∀ c : Fin 27, Fast.CertV ![10, 17, c] 1 := by decide +kernel

theorem L1_10_18 : ∀ c : Fin 27, Fast.CertV ![10, 18, c] 1 := by decide +kernel

theorem L1_10_19 : ∀ c : Fin 27, Fast.CertV ![10, 19, c] 1 := by decide +kernel

theorem L1_10_20 : ∀ c : Fin 27, Fast.CertV ![10, 20, c] 1 := by decide +kernel

theorem L1_10_21 : ∀ c : Fin 27, Fast.CertV ![10, 21, c] 1 := by decide +kernel

theorem L1_10_22 : ∀ c : Fin 27, Fast.CertV ![10, 22, c] 1 := by decide +kernel

theorem L1_10_23 : ∀ c : Fin 27, Fast.CertV ![10, 23, c] 1 := by decide +kernel

theorem L1_10_24 : ∀ c : Fin 27, Fast.CertV ![10, 24, c] 1 := by decide +kernel

theorem L1_10_25 : ∀ c : Fin 27, Fast.CertV ![10, 25, c] 1 := by decide +kernel

theorem L1_10_26 : ∀ c : Fin 27, Fast.CertV ![10, 26, c] 1 := by decide +kernel

theorem A1_10 : ∀ b c : Fin 27, Fast.CertV ![10, b, c] 1
  | ⟨0, _⟩ => L1_10_0
  | ⟨1, _⟩ => L1_10_1
  | ⟨2, _⟩ => L1_10_2
  | ⟨3, _⟩ => L1_10_3
  | ⟨4, _⟩ => L1_10_4
  | ⟨5, _⟩ => L1_10_5
  | ⟨6, _⟩ => L1_10_6
  | ⟨7, _⟩ => L1_10_7
  | ⟨8, _⟩ => L1_10_8
  | ⟨9, _⟩ => L1_10_9
  | ⟨10, _⟩ => L1_10_10
  | ⟨11, _⟩ => L1_10_11
  | ⟨12, _⟩ => L1_10_12
  | ⟨13, _⟩ => L1_10_13
  | ⟨14, _⟩ => L1_10_14
  | ⟨15, _⟩ => L1_10_15
  | ⟨16, _⟩ => L1_10_16
  | ⟨17, _⟩ => L1_10_17
  | ⟨18, _⟩ => L1_10_18
  | ⟨19, _⟩ => L1_10_19
  | ⟨20, _⟩ => L1_10_20
  | ⟨21, _⟩ => L1_10_21
  | ⟨22, _⟩ => L1_10_22
  | ⟨23, _⟩ => L1_10_23
  | ⟨24, _⟩ => L1_10_24
  | ⟨25, _⟩ => L1_10_25
  | ⟨26, _⟩ => L1_10_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_11_0 : ∀ c : Fin 27, Fast.CertV ![11, 0, c] 1 := by decide +kernel

theorem L1_11_1 : ∀ c : Fin 27, Fast.CertV ![11, 1, c] 1 := by decide +kernel

theorem L1_11_2 : ∀ c : Fin 27, Fast.CertV ![11, 2, c] 1 := by decide +kernel

theorem L1_11_3 : ∀ c : Fin 27, Fast.CertV ![11, 3, c] 1 := by decide +kernel

theorem L1_11_4 : ∀ c : Fin 27, Fast.CertV ![11, 4, c] 1 := by decide +kernel

theorem L1_11_5 : ∀ c : Fin 27, Fast.CertV ![11, 5, c] 1 := by decide +kernel

theorem L1_11_6 : ∀ c : Fin 27, Fast.CertV ![11, 6, c] 1 := by decide +kernel

theorem L1_11_7 : ∀ c : Fin 27, Fast.CertV ![11, 7, c] 1 := by decide +kernel

theorem L1_11_8 : ∀ c : Fin 27, Fast.CertV ![11, 8, c] 1 := by decide +kernel

theorem L1_11_9 : ∀ c : Fin 27, Fast.CertV ![11, 9, c] 1 := by decide +kernel

theorem L1_11_10 : ∀ c : Fin 27, Fast.CertV ![11, 10, c] 1 := by decide +kernel

theorem L1_11_11 : ∀ c : Fin 27, Fast.CertV ![11, 11, c] 1 := by decide +kernel

theorem L1_11_12 : ∀ c : Fin 27, Fast.CertV ![11, 12, c] 1 := by decide +kernel

theorem L1_11_13 : ∀ c : Fin 27, Fast.CertV ![11, 13, c] 1 := by decide +kernel

theorem L1_11_14 : ∀ c : Fin 27, Fast.CertV ![11, 14, c] 1 := by decide +kernel

theorem L1_11_15 : ∀ c : Fin 27, Fast.CertV ![11, 15, c] 1 := by decide +kernel

theorem L1_11_16 : ∀ c : Fin 27, Fast.CertV ![11, 16, c] 1 := by decide +kernel

theorem L1_11_17 : ∀ c : Fin 27, Fast.CertV ![11, 17, c] 1 := by decide +kernel

theorem L1_11_18 : ∀ c : Fin 27, Fast.CertV ![11, 18, c] 1 := by decide +kernel

theorem L1_11_19 : ∀ c : Fin 27, Fast.CertV ![11, 19, c] 1 := by decide +kernel

theorem L1_11_20 : ∀ c : Fin 27, Fast.CertV ![11, 20, c] 1 := by decide +kernel

theorem L1_11_21 : ∀ c : Fin 27, Fast.CertV ![11, 21, c] 1 := by decide +kernel

theorem L1_11_22 : ∀ c : Fin 27, Fast.CertV ![11, 22, c] 1 := by decide +kernel

theorem L1_11_23 : ∀ c : Fin 27, Fast.CertV ![11, 23, c] 1 := by decide +kernel

theorem L1_11_24 : ∀ c : Fin 27, Fast.CertV ![11, 24, c] 1 := by decide +kernel

theorem L1_11_25 : ∀ c : Fin 27, Fast.CertV ![11, 25, c] 1 := by decide +kernel

theorem L1_11_26 : ∀ c : Fin 27, Fast.CertV ![11, 26, c] 1 := by decide +kernel

theorem A1_11 : ∀ b c : Fin 27, Fast.CertV ![11, b, c] 1
  | ⟨0, _⟩ => L1_11_0
  | ⟨1, _⟩ => L1_11_1
  | ⟨2, _⟩ => L1_11_2
  | ⟨3, _⟩ => L1_11_3
  | ⟨4, _⟩ => L1_11_4
  | ⟨5, _⟩ => L1_11_5
  | ⟨6, _⟩ => L1_11_6
  | ⟨7, _⟩ => L1_11_7
  | ⟨8, _⟩ => L1_11_8
  | ⟨9, _⟩ => L1_11_9
  | ⟨10, _⟩ => L1_11_10
  | ⟨11, _⟩ => L1_11_11
  | ⟨12, _⟩ => L1_11_12
  | ⟨13, _⟩ => L1_11_13
  | ⟨14, _⟩ => L1_11_14
  | ⟨15, _⟩ => L1_11_15
  | ⟨16, _⟩ => L1_11_16
  | ⟨17, _⟩ => L1_11_17
  | ⟨18, _⟩ => L1_11_18
  | ⟨19, _⟩ => L1_11_19
  | ⟨20, _⟩ => L1_11_20
  | ⟨21, _⟩ => L1_11_21
  | ⟨22, _⟩ => L1_11_22
  | ⟨23, _⟩ => L1_11_23
  | ⟨24, _⟩ => L1_11_24
  | ⟨25, _⟩ => L1_11_25
  | ⟨26, _⟩ => L1_11_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_12_0 : ∀ c : Fin 27, Fast.CertV ![12, 0, c] 1 := by decide +kernel

theorem L1_12_1 : ∀ c : Fin 27, Fast.CertV ![12, 1, c] 1 := by decide +kernel

theorem L1_12_2 : ∀ c : Fin 27, Fast.CertV ![12, 2, c] 1 := by decide +kernel

theorem L1_12_3 : ∀ c : Fin 27, Fast.CertV ![12, 3, c] 1 := by decide +kernel

theorem L1_12_4 : ∀ c : Fin 27, Fast.CertV ![12, 4, c] 1 := by decide +kernel

theorem L1_12_5 : ∀ c : Fin 27, Fast.CertV ![12, 5, c] 1 := by decide +kernel

theorem L1_12_6 : ∀ c : Fin 27, Fast.CertV ![12, 6, c] 1 := by decide +kernel

theorem L1_12_7 : ∀ c : Fin 27, Fast.CertV ![12, 7, c] 1 := by decide +kernel

theorem L1_12_8 : ∀ c : Fin 27, Fast.CertV ![12, 8, c] 1 := by decide +kernel

theorem L1_12_9 : ∀ c : Fin 27, Fast.CertV ![12, 9, c] 1 := by decide +kernel

theorem L1_12_10 : ∀ c : Fin 27, Fast.CertV ![12, 10, c] 1 := by decide +kernel

theorem L1_12_11 : ∀ c : Fin 27, Fast.CertV ![12, 11, c] 1 := by decide +kernel

theorem L1_12_12 : ∀ c : Fin 27, Fast.CertV ![12, 12, c] 1 := by decide +kernel

theorem L1_12_13 : ∀ c : Fin 27, Fast.CertV ![12, 13, c] 1 := by decide +kernel

theorem L1_12_14 : ∀ c : Fin 27, Fast.CertV ![12, 14, c] 1 := by decide +kernel

theorem L1_12_15 : ∀ c : Fin 27, Fast.CertV ![12, 15, c] 1 := by decide +kernel

theorem L1_12_16 : ∀ c : Fin 27, Fast.CertV ![12, 16, c] 1 := by decide +kernel

theorem L1_12_17 : ∀ c : Fin 27, Fast.CertV ![12, 17, c] 1 := by decide +kernel

theorem L1_12_18 : ∀ c : Fin 27, Fast.CertV ![12, 18, c] 1 := by decide +kernel

theorem L1_12_19 : ∀ c : Fin 27, Fast.CertV ![12, 19, c] 1 := by decide +kernel

theorem L1_12_20 : ∀ c : Fin 27, Fast.CertV ![12, 20, c] 1 := by decide +kernel

theorem L1_12_21 : ∀ c : Fin 27, Fast.CertV ![12, 21, c] 1 := by decide +kernel

theorem L1_12_22 : ∀ c : Fin 27, Fast.CertV ![12, 22, c] 1 := by decide +kernel

theorem L1_12_23 : ∀ c : Fin 27, Fast.CertV ![12, 23, c] 1 := by decide +kernel

theorem L1_12_24 : ∀ c : Fin 27, Fast.CertV ![12, 24, c] 1 := by decide +kernel

theorem L1_12_25 : ∀ c : Fin 27, Fast.CertV ![12, 25, c] 1 := by decide +kernel

theorem L1_12_26 : ∀ c : Fin 27, Fast.CertV ![12, 26, c] 1 := by decide +kernel

theorem A1_12 : ∀ b c : Fin 27, Fast.CertV ![12, b, c] 1
  | ⟨0, _⟩ => L1_12_0
  | ⟨1, _⟩ => L1_12_1
  | ⟨2, _⟩ => L1_12_2
  | ⟨3, _⟩ => L1_12_3
  | ⟨4, _⟩ => L1_12_4
  | ⟨5, _⟩ => L1_12_5
  | ⟨6, _⟩ => L1_12_6
  | ⟨7, _⟩ => L1_12_7
  | ⟨8, _⟩ => L1_12_8
  | ⟨9, _⟩ => L1_12_9
  | ⟨10, _⟩ => L1_12_10
  | ⟨11, _⟩ => L1_12_11
  | ⟨12, _⟩ => L1_12_12
  | ⟨13, _⟩ => L1_12_13
  | ⟨14, _⟩ => L1_12_14
  | ⟨15, _⟩ => L1_12_15
  | ⟨16, _⟩ => L1_12_16
  | ⟨17, _⟩ => L1_12_17
  | ⟨18, _⟩ => L1_12_18
  | ⟨19, _⟩ => L1_12_19
  | ⟨20, _⟩ => L1_12_20
  | ⟨21, _⟩ => L1_12_21
  | ⟨22, _⟩ => L1_12_22
  | ⟨23, _⟩ => L1_12_23
  | ⟨24, _⟩ => L1_12_24
  | ⟨25, _⟩ => L1_12_25
  | ⟨26, _⟩ => L1_12_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_13_0 : ∀ c : Fin 27, Fast.CertV ![13, 0, c] 1 := by decide +kernel

theorem L1_13_1 : ∀ c : Fin 27, Fast.CertV ![13, 1, c] 1 := by decide +kernel

theorem L1_13_2 : ∀ c : Fin 27, Fast.CertV ![13, 2, c] 1 := by decide +kernel

theorem L1_13_3 : ∀ c : Fin 27, Fast.CertV ![13, 3, c] 1 := by decide +kernel

theorem L1_13_4 : ∀ c : Fin 27, Fast.CertV ![13, 4, c] 1 := by decide +kernel

theorem L1_13_5 : ∀ c : Fin 27, Fast.CertV ![13, 5, c] 1 := by decide +kernel

theorem L1_13_6 : ∀ c : Fin 27, Fast.CertV ![13, 6, c] 1 := by decide +kernel

theorem L1_13_7 : ∀ c : Fin 27, Fast.CertV ![13, 7, c] 1 := by decide +kernel

theorem L1_13_8 : ∀ c : Fin 27, Fast.CertV ![13, 8, c] 1 := by decide +kernel

theorem L1_13_9 : ∀ c : Fin 27, Fast.CertV ![13, 9, c] 1 := by decide +kernel

theorem L1_13_10 : ∀ c : Fin 27, Fast.CertV ![13, 10, c] 1 := by decide +kernel

theorem L1_13_11 : ∀ c : Fin 27, Fast.CertV ![13, 11, c] 1 := by decide +kernel

theorem L1_13_12 : ∀ c : Fin 27, Fast.CertV ![13, 12, c] 1 := by decide +kernel

theorem L1_13_13 : ∀ c : Fin 27, Fast.CertV ![13, 13, c] 1 := by decide +kernel

theorem L1_13_14 : ∀ c : Fin 27, Fast.CertV ![13, 14, c] 1 := by decide +kernel

theorem L1_13_15 : ∀ c : Fin 27, Fast.CertV ![13, 15, c] 1 := by decide +kernel

theorem L1_13_16 : ∀ c : Fin 27, Fast.CertV ![13, 16, c] 1 := by decide +kernel

theorem L1_13_17 : ∀ c : Fin 27, Fast.CertV ![13, 17, c] 1 := by decide +kernel

theorem L1_13_18 : ∀ c : Fin 27, Fast.CertV ![13, 18, c] 1 := by decide +kernel

theorem L1_13_19 : ∀ c : Fin 27, Fast.CertV ![13, 19, c] 1 := by decide +kernel

theorem L1_13_20 : ∀ c : Fin 27, Fast.CertV ![13, 20, c] 1 := by decide +kernel

theorem L1_13_21 : ∀ c : Fin 27, Fast.CertV ![13, 21, c] 1 := by decide +kernel

theorem L1_13_22 : ∀ c : Fin 27, Fast.CertV ![13, 22, c] 1 := by decide +kernel

theorem L1_13_23 : ∀ c : Fin 27, Fast.CertV ![13, 23, c] 1 := by decide +kernel

theorem L1_13_24 : ∀ c : Fin 27, Fast.CertV ![13, 24, c] 1 := by decide +kernel

theorem L1_13_25 : ∀ c : Fin 27, Fast.CertV ![13, 25, c] 1 := by decide +kernel

theorem L1_13_26 : ∀ c : Fin 27, Fast.CertV ![13, 26, c] 1 := by decide +kernel

theorem A1_13 : ∀ b c : Fin 27, Fast.CertV ![13, b, c] 1
  | ⟨0, _⟩ => L1_13_0
  | ⟨1, _⟩ => L1_13_1
  | ⟨2, _⟩ => L1_13_2
  | ⟨3, _⟩ => L1_13_3
  | ⟨4, _⟩ => L1_13_4
  | ⟨5, _⟩ => L1_13_5
  | ⟨6, _⟩ => L1_13_6
  | ⟨7, _⟩ => L1_13_7
  | ⟨8, _⟩ => L1_13_8
  | ⟨9, _⟩ => L1_13_9
  | ⟨10, _⟩ => L1_13_10
  | ⟨11, _⟩ => L1_13_11
  | ⟨12, _⟩ => L1_13_12
  | ⟨13, _⟩ => L1_13_13
  | ⟨14, _⟩ => L1_13_14
  | ⟨15, _⟩ => L1_13_15
  | ⟨16, _⟩ => L1_13_16
  | ⟨17, _⟩ => L1_13_17
  | ⟨18, _⟩ => L1_13_18
  | ⟨19, _⟩ => L1_13_19
  | ⟨20, _⟩ => L1_13_20
  | ⟨21, _⟩ => L1_13_21
  | ⟨22, _⟩ => L1_13_22
  | ⟨23, _⟩ => L1_13_23
  | ⟨24, _⟩ => L1_13_24
  | ⟨25, _⟩ => L1_13_25
  | ⟨26, _⟩ => L1_13_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_14_0 : ∀ c : Fin 27, Fast.CertV ![14, 0, c] 1 := by decide +kernel

theorem L1_14_1 : ∀ c : Fin 27, Fast.CertV ![14, 1, c] 1 := by decide +kernel

theorem L1_14_2 : ∀ c : Fin 27, Fast.CertV ![14, 2, c] 1 := by decide +kernel

theorem L1_14_3 : ∀ c : Fin 27, Fast.CertV ![14, 3, c] 1 := by decide +kernel

theorem L1_14_4 : ∀ c : Fin 27, Fast.CertV ![14, 4, c] 1 := by decide +kernel

theorem L1_14_5 : ∀ c : Fin 27, Fast.CertV ![14, 5, c] 1 := by decide +kernel

theorem L1_14_6 : ∀ c : Fin 27, Fast.CertV ![14, 6, c] 1 := by decide +kernel

theorem L1_14_7 : ∀ c : Fin 27, Fast.CertV ![14, 7, c] 1 := by decide +kernel

theorem L1_14_8 : ∀ c : Fin 27, Fast.CertV ![14, 8, c] 1 := by decide +kernel

theorem L1_14_9 : ∀ c : Fin 27, Fast.CertV ![14, 9, c] 1 := by decide +kernel

theorem L1_14_10 : ∀ c : Fin 27, Fast.CertV ![14, 10, c] 1 := by decide +kernel

theorem L1_14_11 : ∀ c : Fin 27, Fast.CertV ![14, 11, c] 1 := by decide +kernel

theorem L1_14_12 : ∀ c : Fin 27, Fast.CertV ![14, 12, c] 1 := by decide +kernel

theorem L1_14_13 : ∀ c : Fin 27, Fast.CertV ![14, 13, c] 1 := by decide +kernel

theorem L1_14_14 : ∀ c : Fin 27, Fast.CertV ![14, 14, c] 1 := by decide +kernel

theorem L1_14_15 : ∀ c : Fin 27, Fast.CertV ![14, 15, c] 1 := by decide +kernel

theorem L1_14_16 : ∀ c : Fin 27, Fast.CertV ![14, 16, c] 1 := by decide +kernel

theorem L1_14_17 : ∀ c : Fin 27, Fast.CertV ![14, 17, c] 1 := by decide +kernel

theorem L1_14_18 : ∀ c : Fin 27, Fast.CertV ![14, 18, c] 1 := by decide +kernel

theorem L1_14_19 : ∀ c : Fin 27, Fast.CertV ![14, 19, c] 1 := by decide +kernel

theorem L1_14_20 : ∀ c : Fin 27, Fast.CertV ![14, 20, c] 1 := by decide +kernel

theorem L1_14_21 : ∀ c : Fin 27, Fast.CertV ![14, 21, c] 1 := by decide +kernel

theorem L1_14_22 : ∀ c : Fin 27, Fast.CertV ![14, 22, c] 1 := by decide +kernel

theorem L1_14_23 : ∀ c : Fin 27, Fast.CertV ![14, 23, c] 1 := by decide +kernel

theorem L1_14_24 : ∀ c : Fin 27, Fast.CertV ![14, 24, c] 1 := by decide +kernel

theorem L1_14_25 : ∀ c : Fin 27, Fast.CertV ![14, 25, c] 1 := by decide +kernel

theorem L1_14_26 : ∀ c : Fin 27, Fast.CertV ![14, 26, c] 1 := by decide +kernel

theorem A1_14 : ∀ b c : Fin 27, Fast.CertV ![14, b, c] 1
  | ⟨0, _⟩ => L1_14_0
  | ⟨1, _⟩ => L1_14_1
  | ⟨2, _⟩ => L1_14_2
  | ⟨3, _⟩ => L1_14_3
  | ⟨4, _⟩ => L1_14_4
  | ⟨5, _⟩ => L1_14_5
  | ⟨6, _⟩ => L1_14_6
  | ⟨7, _⟩ => L1_14_7
  | ⟨8, _⟩ => L1_14_8
  | ⟨9, _⟩ => L1_14_9
  | ⟨10, _⟩ => L1_14_10
  | ⟨11, _⟩ => L1_14_11
  | ⟨12, _⟩ => L1_14_12
  | ⟨13, _⟩ => L1_14_13
  | ⟨14, _⟩ => L1_14_14
  | ⟨15, _⟩ => L1_14_15
  | ⟨16, _⟩ => L1_14_16
  | ⟨17, _⟩ => L1_14_17
  | ⟨18, _⟩ => L1_14_18
  | ⟨19, _⟩ => L1_14_19
  | ⟨20, _⟩ => L1_14_20
  | ⟨21, _⟩ => L1_14_21
  | ⟨22, _⟩ => L1_14_22
  | ⟨23, _⟩ => L1_14_23
  | ⟨24, _⟩ => L1_14_24
  | ⟨25, _⟩ => L1_14_25
  | ⟨26, _⟩ => L1_14_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_15_0 : ∀ c : Fin 27, Fast.CertV ![15, 0, c] 1 := by decide +kernel

theorem L1_15_1 : ∀ c : Fin 27, Fast.CertV ![15, 1, c] 1 := by decide +kernel

theorem L1_15_2 : ∀ c : Fin 27, Fast.CertV ![15, 2, c] 1 := by decide +kernel

theorem L1_15_3 : ∀ c : Fin 27, Fast.CertV ![15, 3, c] 1 := by decide +kernel

theorem L1_15_4 : ∀ c : Fin 27, Fast.CertV ![15, 4, c] 1 := by decide +kernel

theorem L1_15_5 : ∀ c : Fin 27, Fast.CertV ![15, 5, c] 1 := by decide +kernel

theorem L1_15_6 : ∀ c : Fin 27, Fast.CertV ![15, 6, c] 1 := by decide +kernel

theorem L1_15_7 : ∀ c : Fin 27, Fast.CertV ![15, 7, c] 1 := by decide +kernel

theorem L1_15_8 : ∀ c : Fin 27, Fast.CertV ![15, 8, c] 1 := by decide +kernel

theorem L1_15_9 : ∀ c : Fin 27, Fast.CertV ![15, 9, c] 1 := by decide +kernel

theorem L1_15_10 : ∀ c : Fin 27, Fast.CertV ![15, 10, c] 1 := by decide +kernel

theorem L1_15_11 : ∀ c : Fin 27, Fast.CertV ![15, 11, c] 1 := by decide +kernel

theorem L1_15_12 : ∀ c : Fin 27, Fast.CertV ![15, 12, c] 1 := by decide +kernel

theorem L1_15_13 : ∀ c : Fin 27, Fast.CertV ![15, 13, c] 1 := by decide +kernel

theorem L1_15_14 : ∀ c : Fin 27, Fast.CertV ![15, 14, c] 1 := by decide +kernel

theorem L1_15_15 : ∀ c : Fin 27, Fast.CertV ![15, 15, c] 1 := by decide +kernel

theorem L1_15_16 : ∀ c : Fin 27, Fast.CertV ![15, 16, c] 1 := by decide +kernel

theorem L1_15_17 : ∀ c : Fin 27, Fast.CertV ![15, 17, c] 1 := by decide +kernel

theorem L1_15_18 : ∀ c : Fin 27, Fast.CertV ![15, 18, c] 1 := by decide +kernel

theorem L1_15_19 : ∀ c : Fin 27, Fast.CertV ![15, 19, c] 1 := by decide +kernel

theorem L1_15_20 : ∀ c : Fin 27, Fast.CertV ![15, 20, c] 1 := by decide +kernel

theorem L1_15_21 : ∀ c : Fin 27, Fast.CertV ![15, 21, c] 1 := by decide +kernel

theorem L1_15_22 : ∀ c : Fin 27, Fast.CertV ![15, 22, c] 1 := by decide +kernel

theorem L1_15_23 : ∀ c : Fin 27, Fast.CertV ![15, 23, c] 1 := by decide +kernel

theorem L1_15_24 : ∀ c : Fin 27, Fast.CertV ![15, 24, c] 1 := by decide +kernel

theorem L1_15_25 : ∀ c : Fin 27, Fast.CertV ![15, 25, c] 1 := by decide +kernel

theorem L1_15_26 : ∀ c : Fin 27, Fast.CertV ![15, 26, c] 1 := by decide +kernel

theorem A1_15 : ∀ b c : Fin 27, Fast.CertV ![15, b, c] 1
  | ⟨0, _⟩ => L1_15_0
  | ⟨1, _⟩ => L1_15_1
  | ⟨2, _⟩ => L1_15_2
  | ⟨3, _⟩ => L1_15_3
  | ⟨4, _⟩ => L1_15_4
  | ⟨5, _⟩ => L1_15_5
  | ⟨6, _⟩ => L1_15_6
  | ⟨7, _⟩ => L1_15_7
  | ⟨8, _⟩ => L1_15_8
  | ⟨9, _⟩ => L1_15_9
  | ⟨10, _⟩ => L1_15_10
  | ⟨11, _⟩ => L1_15_11
  | ⟨12, _⟩ => L1_15_12
  | ⟨13, _⟩ => L1_15_13
  | ⟨14, _⟩ => L1_15_14
  | ⟨15, _⟩ => L1_15_15
  | ⟨16, _⟩ => L1_15_16
  | ⟨17, _⟩ => L1_15_17
  | ⟨18, _⟩ => L1_15_18
  | ⟨19, _⟩ => L1_15_19
  | ⟨20, _⟩ => L1_15_20
  | ⟨21, _⟩ => L1_15_21
  | ⟨22, _⟩ => L1_15_22
  | ⟨23, _⟩ => L1_15_23
  | ⟨24, _⟩ => L1_15_24
  | ⟨25, _⟩ => L1_15_25
  | ⟨26, _⟩ => L1_15_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_16_0 : ∀ c : Fin 27, Fast.CertV ![16, 0, c] 1 := by decide +kernel

theorem L1_16_1 : ∀ c : Fin 27, Fast.CertV ![16, 1, c] 1 := by decide +kernel

theorem L1_16_2 : ∀ c : Fin 27, Fast.CertV ![16, 2, c] 1 := by decide +kernel

theorem L1_16_3 : ∀ c : Fin 27, Fast.CertV ![16, 3, c] 1 := by decide +kernel

theorem L1_16_4 : ∀ c : Fin 27, Fast.CertV ![16, 4, c] 1 := by decide +kernel

theorem L1_16_5 : ∀ c : Fin 27, Fast.CertV ![16, 5, c] 1 := by decide +kernel

theorem L1_16_6 : ∀ c : Fin 27, Fast.CertV ![16, 6, c] 1 := by decide +kernel

theorem L1_16_7 : ∀ c : Fin 27, Fast.CertV ![16, 7, c] 1 := by decide +kernel

theorem L1_16_8 : ∀ c : Fin 27, Fast.CertV ![16, 8, c] 1 := by decide +kernel

theorem L1_16_9 : ∀ c : Fin 27, Fast.CertV ![16, 9, c] 1 := by decide +kernel

theorem L1_16_10 : ∀ c : Fin 27, Fast.CertV ![16, 10, c] 1 := by decide +kernel

theorem L1_16_11 : ∀ c : Fin 27, Fast.CertV ![16, 11, c] 1 := by decide +kernel

theorem L1_16_12 : ∀ c : Fin 27, Fast.CertV ![16, 12, c] 1 := by decide +kernel

theorem L1_16_13 : ∀ c : Fin 27, Fast.CertV ![16, 13, c] 1 := by decide +kernel

theorem L1_16_14 : ∀ c : Fin 27, Fast.CertV ![16, 14, c] 1 := by decide +kernel

theorem L1_16_15 : ∀ c : Fin 27, Fast.CertV ![16, 15, c] 1 := by decide +kernel

theorem L1_16_16 : ∀ c : Fin 27, Fast.CertV ![16, 16, c] 1 := by decide +kernel

theorem L1_16_17 : ∀ c : Fin 27, Fast.CertV ![16, 17, c] 1 := by decide +kernel

theorem L1_16_18 : ∀ c : Fin 27, Fast.CertV ![16, 18, c] 1 := by decide +kernel

theorem L1_16_19 : ∀ c : Fin 27, Fast.CertV ![16, 19, c] 1 := by decide +kernel

theorem L1_16_20 : ∀ c : Fin 27, Fast.CertV ![16, 20, c] 1 := by decide +kernel

theorem L1_16_21 : ∀ c : Fin 27, Fast.CertV ![16, 21, c] 1 := by decide +kernel

theorem L1_16_22 : ∀ c : Fin 27, Fast.CertV ![16, 22, c] 1 := by decide +kernel

theorem L1_16_23 : ∀ c : Fin 27, Fast.CertV ![16, 23, c] 1 := by decide +kernel

theorem L1_16_24 : ∀ c : Fin 27, Fast.CertV ![16, 24, c] 1 := by decide +kernel

theorem L1_16_25 : ∀ c : Fin 27, Fast.CertV ![16, 25, c] 1 := by decide +kernel

theorem L1_16_26 : ∀ c : Fin 27, Fast.CertV ![16, 26, c] 1 := by decide +kernel

theorem A1_16 : ∀ b c : Fin 27, Fast.CertV ![16, b, c] 1
  | ⟨0, _⟩ => L1_16_0
  | ⟨1, _⟩ => L1_16_1
  | ⟨2, _⟩ => L1_16_2
  | ⟨3, _⟩ => L1_16_3
  | ⟨4, _⟩ => L1_16_4
  | ⟨5, _⟩ => L1_16_5
  | ⟨6, _⟩ => L1_16_6
  | ⟨7, _⟩ => L1_16_7
  | ⟨8, _⟩ => L1_16_8
  | ⟨9, _⟩ => L1_16_9
  | ⟨10, _⟩ => L1_16_10
  | ⟨11, _⟩ => L1_16_11
  | ⟨12, _⟩ => L1_16_12
  | ⟨13, _⟩ => L1_16_13
  | ⟨14, _⟩ => L1_16_14
  | ⟨15, _⟩ => L1_16_15
  | ⟨16, _⟩ => L1_16_16
  | ⟨17, _⟩ => L1_16_17
  | ⟨18, _⟩ => L1_16_18
  | ⟨19, _⟩ => L1_16_19
  | ⟨20, _⟩ => L1_16_20
  | ⟨21, _⟩ => L1_16_21
  | ⟨22, _⟩ => L1_16_22
  | ⟨23, _⟩ => L1_16_23
  | ⟨24, _⟩ => L1_16_24
  | ⟨25, _⟩ => L1_16_25
  | ⟨26, _⟩ => L1_16_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_17_0 : ∀ c : Fin 27, Fast.CertV ![17, 0, c] 1 := by decide +kernel

theorem L1_17_1 : ∀ c : Fin 27, Fast.CertV ![17, 1, c] 1 := by decide +kernel

theorem L1_17_2 : ∀ c : Fin 27, Fast.CertV ![17, 2, c] 1 := by decide +kernel

theorem L1_17_3 : ∀ c : Fin 27, Fast.CertV ![17, 3, c] 1 := by decide +kernel

theorem L1_17_4 : ∀ c : Fin 27, Fast.CertV ![17, 4, c] 1 := by decide +kernel

theorem L1_17_5 : ∀ c : Fin 27, Fast.CertV ![17, 5, c] 1 := by decide +kernel

theorem L1_17_6 : ∀ c : Fin 27, Fast.CertV ![17, 6, c] 1 := by decide +kernel

theorem L1_17_7 : ∀ c : Fin 27, Fast.CertV ![17, 7, c] 1 := by decide +kernel

theorem L1_17_8 : ∀ c : Fin 27, Fast.CertV ![17, 8, c] 1 := by decide +kernel

theorem L1_17_9 : ∀ c : Fin 27, Fast.CertV ![17, 9, c] 1 := by decide +kernel

theorem L1_17_10 : ∀ c : Fin 27, Fast.CertV ![17, 10, c] 1 := by decide +kernel

theorem L1_17_11 : ∀ c : Fin 27, Fast.CertV ![17, 11, c] 1 := by decide +kernel

theorem L1_17_12 : ∀ c : Fin 27, Fast.CertV ![17, 12, c] 1 := by decide +kernel

theorem L1_17_13 : ∀ c : Fin 27, Fast.CertV ![17, 13, c] 1 := by decide +kernel

theorem L1_17_14 : ∀ c : Fin 27, Fast.CertV ![17, 14, c] 1 := by decide +kernel

theorem L1_17_15 : ∀ c : Fin 27, Fast.CertV ![17, 15, c] 1 := by decide +kernel

theorem L1_17_16 : ∀ c : Fin 27, Fast.CertV ![17, 16, c] 1 := by decide +kernel

theorem L1_17_17 : ∀ c : Fin 27, Fast.CertV ![17, 17, c] 1 := by decide +kernel

theorem L1_17_18 : ∀ c : Fin 27, Fast.CertV ![17, 18, c] 1 := by decide +kernel

theorem L1_17_19 : ∀ c : Fin 27, Fast.CertV ![17, 19, c] 1 := by decide +kernel

theorem L1_17_20 : ∀ c : Fin 27, Fast.CertV ![17, 20, c] 1 := by decide +kernel

theorem L1_17_21 : ∀ c : Fin 27, Fast.CertV ![17, 21, c] 1 := by decide +kernel

theorem L1_17_22 : ∀ c : Fin 27, Fast.CertV ![17, 22, c] 1 := by decide +kernel

theorem L1_17_23 : ∀ c : Fin 27, Fast.CertV ![17, 23, c] 1 := by decide +kernel

theorem L1_17_24 : ∀ c : Fin 27, Fast.CertV ![17, 24, c] 1 := by decide +kernel

theorem L1_17_25 : ∀ c : Fin 27, Fast.CertV ![17, 25, c] 1 := by decide +kernel

theorem L1_17_26 : ∀ c : Fin 27, Fast.CertV ![17, 26, c] 1 := by decide +kernel

theorem A1_17 : ∀ b c : Fin 27, Fast.CertV ![17, b, c] 1
  | ⟨0, _⟩ => L1_17_0
  | ⟨1, _⟩ => L1_17_1
  | ⟨2, _⟩ => L1_17_2
  | ⟨3, _⟩ => L1_17_3
  | ⟨4, _⟩ => L1_17_4
  | ⟨5, _⟩ => L1_17_5
  | ⟨6, _⟩ => L1_17_6
  | ⟨7, _⟩ => L1_17_7
  | ⟨8, _⟩ => L1_17_8
  | ⟨9, _⟩ => L1_17_9
  | ⟨10, _⟩ => L1_17_10
  | ⟨11, _⟩ => L1_17_11
  | ⟨12, _⟩ => L1_17_12
  | ⟨13, _⟩ => L1_17_13
  | ⟨14, _⟩ => L1_17_14
  | ⟨15, _⟩ => L1_17_15
  | ⟨16, _⟩ => L1_17_16
  | ⟨17, _⟩ => L1_17_17
  | ⟨18, _⟩ => L1_17_18
  | ⟨19, _⟩ => L1_17_19
  | ⟨20, _⟩ => L1_17_20
  | ⟨21, _⟩ => L1_17_21
  | ⟨22, _⟩ => L1_17_22
  | ⟨23, _⟩ => L1_17_23
  | ⟨24, _⟩ => L1_17_24
  | ⟨25, _⟩ => L1_17_25
  | ⟨26, _⟩ => L1_17_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

end E1Cert.Table
