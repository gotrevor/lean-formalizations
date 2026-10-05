/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.E1CertCore

/-! Kernel table for `E1Cert.cert_all`: `t = 1`, `a ∈ [18, 27)`. -/

namespace E1Cert.Table

set_option maxRecDepth 100000

theorem L1_18_0 : ∀ c : Fin 27, Fast.CertV ![18, 0, c] 1 := by decide +kernel

theorem L1_18_1 : ∀ c : Fin 27, Fast.CertV ![18, 1, c] 1 := by decide +kernel

theorem L1_18_2 : ∀ c : Fin 27, Fast.CertV ![18, 2, c] 1 := by decide +kernel

theorem L1_18_3 : ∀ c : Fin 27, Fast.CertV ![18, 3, c] 1 := by decide +kernel

theorem L1_18_4 : ∀ c : Fin 27, Fast.CertV ![18, 4, c] 1 := by decide +kernel

theorem L1_18_5 : ∀ c : Fin 27, Fast.CertV ![18, 5, c] 1 := by decide +kernel

theorem L1_18_6 : ∀ c : Fin 27, Fast.CertV ![18, 6, c] 1 := by decide +kernel

theorem L1_18_7 : ∀ c : Fin 27, Fast.CertV ![18, 7, c] 1 := by decide +kernel

theorem L1_18_8 : ∀ c : Fin 27, Fast.CertV ![18, 8, c] 1 := by decide +kernel

theorem L1_18_9 : ∀ c : Fin 27, Fast.CertV ![18, 9, c] 1 := by decide +kernel

theorem L1_18_10 : ∀ c : Fin 27, Fast.CertV ![18, 10, c] 1 := by decide +kernel

theorem L1_18_11 : ∀ c : Fin 27, Fast.CertV ![18, 11, c] 1 := by decide +kernel

theorem L1_18_12 : ∀ c : Fin 27, Fast.CertV ![18, 12, c] 1 := by decide +kernel

theorem L1_18_13 : ∀ c : Fin 27, Fast.CertV ![18, 13, c] 1 := by decide +kernel

theorem L1_18_14 : ∀ c : Fin 27, Fast.CertV ![18, 14, c] 1 := by decide +kernel

theorem L1_18_15 : ∀ c : Fin 27, Fast.CertV ![18, 15, c] 1 := by decide +kernel

theorem L1_18_16 : ∀ c : Fin 27, Fast.CertV ![18, 16, c] 1 := by decide +kernel

theorem L1_18_17 : ∀ c : Fin 27, Fast.CertV ![18, 17, c] 1 := by decide +kernel

theorem L1_18_18 : ∀ c : Fin 27, Fast.CertV ![18, 18, c] 1 := by decide +kernel

theorem L1_18_19 : ∀ c : Fin 27, Fast.CertV ![18, 19, c] 1 := by decide +kernel

theorem L1_18_20 : ∀ c : Fin 27, Fast.CertV ![18, 20, c] 1 := by decide +kernel

theorem L1_18_21 : ∀ c : Fin 27, Fast.CertV ![18, 21, c] 1 := by decide +kernel

theorem L1_18_22 : ∀ c : Fin 27, Fast.CertV ![18, 22, c] 1 := by decide +kernel

theorem L1_18_23 : ∀ c : Fin 27, Fast.CertV ![18, 23, c] 1 := by decide +kernel

theorem L1_18_24 : ∀ c : Fin 27, Fast.CertV ![18, 24, c] 1 := by decide +kernel

theorem L1_18_25 : ∀ c : Fin 27, Fast.CertV ![18, 25, c] 1 := by decide +kernel

theorem L1_18_26 : ∀ c : Fin 27, Fast.CertV ![18, 26, c] 1 := by decide +kernel

theorem A1_18 : ∀ b c : Fin 27, Fast.CertV ![18, b, c] 1
  | ⟨0, _⟩ => L1_18_0
  | ⟨1, _⟩ => L1_18_1
  | ⟨2, _⟩ => L1_18_2
  | ⟨3, _⟩ => L1_18_3
  | ⟨4, _⟩ => L1_18_4
  | ⟨5, _⟩ => L1_18_5
  | ⟨6, _⟩ => L1_18_6
  | ⟨7, _⟩ => L1_18_7
  | ⟨8, _⟩ => L1_18_8
  | ⟨9, _⟩ => L1_18_9
  | ⟨10, _⟩ => L1_18_10
  | ⟨11, _⟩ => L1_18_11
  | ⟨12, _⟩ => L1_18_12
  | ⟨13, _⟩ => L1_18_13
  | ⟨14, _⟩ => L1_18_14
  | ⟨15, _⟩ => L1_18_15
  | ⟨16, _⟩ => L1_18_16
  | ⟨17, _⟩ => L1_18_17
  | ⟨18, _⟩ => L1_18_18
  | ⟨19, _⟩ => L1_18_19
  | ⟨20, _⟩ => L1_18_20
  | ⟨21, _⟩ => L1_18_21
  | ⟨22, _⟩ => L1_18_22
  | ⟨23, _⟩ => L1_18_23
  | ⟨24, _⟩ => L1_18_24
  | ⟨25, _⟩ => L1_18_25
  | ⟨26, _⟩ => L1_18_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_19_0 : ∀ c : Fin 27, Fast.CertV ![19, 0, c] 1 := by decide +kernel

theorem L1_19_1 : ∀ c : Fin 27, Fast.CertV ![19, 1, c] 1 := by decide +kernel

theorem L1_19_2 : ∀ c : Fin 27, Fast.CertV ![19, 2, c] 1 := by decide +kernel

theorem L1_19_3 : ∀ c : Fin 27, Fast.CertV ![19, 3, c] 1 := by decide +kernel

theorem L1_19_4 : ∀ c : Fin 27, Fast.CertV ![19, 4, c] 1 := by decide +kernel

theorem L1_19_5 : ∀ c : Fin 27, Fast.CertV ![19, 5, c] 1 := by decide +kernel

theorem L1_19_6 : ∀ c : Fin 27, Fast.CertV ![19, 6, c] 1 := by decide +kernel

theorem L1_19_7 : ∀ c : Fin 27, Fast.CertV ![19, 7, c] 1 := by decide +kernel

theorem L1_19_8 : ∀ c : Fin 27, Fast.CertV ![19, 8, c] 1 := by decide +kernel

theorem L1_19_9 : ∀ c : Fin 27, Fast.CertV ![19, 9, c] 1 := by decide +kernel

theorem L1_19_10 : ∀ c : Fin 27, Fast.CertV ![19, 10, c] 1 := by decide +kernel

theorem L1_19_11 : ∀ c : Fin 27, Fast.CertV ![19, 11, c] 1 := by decide +kernel

theorem L1_19_12 : ∀ c : Fin 27, Fast.CertV ![19, 12, c] 1 := by decide +kernel

theorem L1_19_13 : ∀ c : Fin 27, Fast.CertV ![19, 13, c] 1 := by decide +kernel

theorem L1_19_14 : ∀ c : Fin 27, Fast.CertV ![19, 14, c] 1 := by decide +kernel

theorem L1_19_15 : ∀ c : Fin 27, Fast.CertV ![19, 15, c] 1 := by decide +kernel

theorem L1_19_16 : ∀ c : Fin 27, Fast.CertV ![19, 16, c] 1 := by decide +kernel

theorem L1_19_17 : ∀ c : Fin 27, Fast.CertV ![19, 17, c] 1 := by decide +kernel

theorem L1_19_18 : ∀ c : Fin 27, Fast.CertV ![19, 18, c] 1 := by decide +kernel

theorem L1_19_19 : ∀ c : Fin 27, Fast.CertV ![19, 19, c] 1 := by decide +kernel

theorem L1_19_20 : ∀ c : Fin 27, Fast.CertV ![19, 20, c] 1 := by decide +kernel

theorem L1_19_21 : ∀ c : Fin 27, Fast.CertV ![19, 21, c] 1 := by decide +kernel

theorem L1_19_22 : ∀ c : Fin 27, Fast.CertV ![19, 22, c] 1 := by decide +kernel

theorem L1_19_23 : ∀ c : Fin 27, Fast.CertV ![19, 23, c] 1 := by decide +kernel

theorem L1_19_24 : ∀ c : Fin 27, Fast.CertV ![19, 24, c] 1 := by decide +kernel

theorem L1_19_25 : ∀ c : Fin 27, Fast.CertV ![19, 25, c] 1 := by decide +kernel

theorem L1_19_26 : ∀ c : Fin 27, Fast.CertV ![19, 26, c] 1 := by decide +kernel

theorem A1_19 : ∀ b c : Fin 27, Fast.CertV ![19, b, c] 1
  | ⟨0, _⟩ => L1_19_0
  | ⟨1, _⟩ => L1_19_1
  | ⟨2, _⟩ => L1_19_2
  | ⟨3, _⟩ => L1_19_3
  | ⟨4, _⟩ => L1_19_4
  | ⟨5, _⟩ => L1_19_5
  | ⟨6, _⟩ => L1_19_6
  | ⟨7, _⟩ => L1_19_7
  | ⟨8, _⟩ => L1_19_8
  | ⟨9, _⟩ => L1_19_9
  | ⟨10, _⟩ => L1_19_10
  | ⟨11, _⟩ => L1_19_11
  | ⟨12, _⟩ => L1_19_12
  | ⟨13, _⟩ => L1_19_13
  | ⟨14, _⟩ => L1_19_14
  | ⟨15, _⟩ => L1_19_15
  | ⟨16, _⟩ => L1_19_16
  | ⟨17, _⟩ => L1_19_17
  | ⟨18, _⟩ => L1_19_18
  | ⟨19, _⟩ => L1_19_19
  | ⟨20, _⟩ => L1_19_20
  | ⟨21, _⟩ => L1_19_21
  | ⟨22, _⟩ => L1_19_22
  | ⟨23, _⟩ => L1_19_23
  | ⟨24, _⟩ => L1_19_24
  | ⟨25, _⟩ => L1_19_25
  | ⟨26, _⟩ => L1_19_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_20_0 : ∀ c : Fin 27, Fast.CertV ![20, 0, c] 1 := by decide +kernel

theorem L1_20_1 : ∀ c : Fin 27, Fast.CertV ![20, 1, c] 1 := by decide +kernel

theorem L1_20_2 : ∀ c : Fin 27, Fast.CertV ![20, 2, c] 1 := by decide +kernel

theorem L1_20_3 : ∀ c : Fin 27, Fast.CertV ![20, 3, c] 1 := by decide +kernel

theorem L1_20_4 : ∀ c : Fin 27, Fast.CertV ![20, 4, c] 1 := by decide +kernel

theorem L1_20_5 : ∀ c : Fin 27, Fast.CertV ![20, 5, c] 1 := by decide +kernel

theorem L1_20_6 : ∀ c : Fin 27, Fast.CertV ![20, 6, c] 1 := by decide +kernel

theorem L1_20_7 : ∀ c : Fin 27, Fast.CertV ![20, 7, c] 1 := by decide +kernel

theorem L1_20_8 : ∀ c : Fin 27, Fast.CertV ![20, 8, c] 1 := by decide +kernel

theorem L1_20_9 : ∀ c : Fin 27, Fast.CertV ![20, 9, c] 1 := by decide +kernel

theorem L1_20_10 : ∀ c : Fin 27, Fast.CertV ![20, 10, c] 1 := by decide +kernel

theorem L1_20_11 : ∀ c : Fin 27, Fast.CertV ![20, 11, c] 1 := by decide +kernel

theorem L1_20_12 : ∀ c : Fin 27, Fast.CertV ![20, 12, c] 1 := by decide +kernel

theorem L1_20_13 : ∀ c : Fin 27, Fast.CertV ![20, 13, c] 1 := by decide +kernel

theorem L1_20_14 : ∀ c : Fin 27, Fast.CertV ![20, 14, c] 1 := by decide +kernel

theorem L1_20_15 : ∀ c : Fin 27, Fast.CertV ![20, 15, c] 1 := by decide +kernel

theorem L1_20_16 : ∀ c : Fin 27, Fast.CertV ![20, 16, c] 1 := by decide +kernel

theorem L1_20_17 : ∀ c : Fin 27, Fast.CertV ![20, 17, c] 1 := by decide +kernel

theorem L1_20_18 : ∀ c : Fin 27, Fast.CertV ![20, 18, c] 1 := by decide +kernel

theorem L1_20_19 : ∀ c : Fin 27, Fast.CertV ![20, 19, c] 1 := by decide +kernel

theorem L1_20_20 : ∀ c : Fin 27, Fast.CertV ![20, 20, c] 1 := by decide +kernel

theorem L1_20_21 : ∀ c : Fin 27, Fast.CertV ![20, 21, c] 1 := by decide +kernel

theorem L1_20_22 : ∀ c : Fin 27, Fast.CertV ![20, 22, c] 1 := by decide +kernel

theorem L1_20_23 : ∀ c : Fin 27, Fast.CertV ![20, 23, c] 1 := by decide +kernel

theorem L1_20_24 : ∀ c : Fin 27, Fast.CertV ![20, 24, c] 1 := by decide +kernel

theorem L1_20_25 : ∀ c : Fin 27, Fast.CertV ![20, 25, c] 1 := by decide +kernel

theorem L1_20_26 : ∀ c : Fin 27, Fast.CertV ![20, 26, c] 1 := by decide +kernel

theorem A1_20 : ∀ b c : Fin 27, Fast.CertV ![20, b, c] 1
  | ⟨0, _⟩ => L1_20_0
  | ⟨1, _⟩ => L1_20_1
  | ⟨2, _⟩ => L1_20_2
  | ⟨3, _⟩ => L1_20_3
  | ⟨4, _⟩ => L1_20_4
  | ⟨5, _⟩ => L1_20_5
  | ⟨6, _⟩ => L1_20_6
  | ⟨7, _⟩ => L1_20_7
  | ⟨8, _⟩ => L1_20_8
  | ⟨9, _⟩ => L1_20_9
  | ⟨10, _⟩ => L1_20_10
  | ⟨11, _⟩ => L1_20_11
  | ⟨12, _⟩ => L1_20_12
  | ⟨13, _⟩ => L1_20_13
  | ⟨14, _⟩ => L1_20_14
  | ⟨15, _⟩ => L1_20_15
  | ⟨16, _⟩ => L1_20_16
  | ⟨17, _⟩ => L1_20_17
  | ⟨18, _⟩ => L1_20_18
  | ⟨19, _⟩ => L1_20_19
  | ⟨20, _⟩ => L1_20_20
  | ⟨21, _⟩ => L1_20_21
  | ⟨22, _⟩ => L1_20_22
  | ⟨23, _⟩ => L1_20_23
  | ⟨24, _⟩ => L1_20_24
  | ⟨25, _⟩ => L1_20_25
  | ⟨26, _⟩ => L1_20_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_21_0 : ∀ c : Fin 27, Fast.CertV ![21, 0, c] 1 := by decide +kernel

theorem L1_21_1 : ∀ c : Fin 27, Fast.CertV ![21, 1, c] 1 := by decide +kernel

theorem L1_21_2 : ∀ c : Fin 27, Fast.CertV ![21, 2, c] 1 := by decide +kernel

theorem L1_21_3 : ∀ c : Fin 27, Fast.CertV ![21, 3, c] 1 := by decide +kernel

theorem L1_21_4 : ∀ c : Fin 27, Fast.CertV ![21, 4, c] 1 := by decide +kernel

theorem L1_21_5 : ∀ c : Fin 27, Fast.CertV ![21, 5, c] 1 := by decide +kernel

theorem L1_21_6 : ∀ c : Fin 27, Fast.CertV ![21, 6, c] 1 := by decide +kernel

theorem L1_21_7 : ∀ c : Fin 27, Fast.CertV ![21, 7, c] 1 := by decide +kernel

theorem L1_21_8 : ∀ c : Fin 27, Fast.CertV ![21, 8, c] 1 := by decide +kernel

theorem L1_21_9 : ∀ c : Fin 27, Fast.CertV ![21, 9, c] 1 := by decide +kernel

theorem L1_21_10 : ∀ c : Fin 27, Fast.CertV ![21, 10, c] 1 := by decide +kernel

theorem L1_21_11 : ∀ c : Fin 27, Fast.CertV ![21, 11, c] 1 := by decide +kernel

theorem L1_21_12 : ∀ c : Fin 27, Fast.CertV ![21, 12, c] 1 := by decide +kernel

theorem L1_21_13 : ∀ c : Fin 27, Fast.CertV ![21, 13, c] 1 := by decide +kernel

theorem L1_21_14 : ∀ c : Fin 27, Fast.CertV ![21, 14, c] 1 := by decide +kernel

theorem L1_21_15 : ∀ c : Fin 27, Fast.CertV ![21, 15, c] 1 := by decide +kernel

theorem L1_21_16 : ∀ c : Fin 27, Fast.CertV ![21, 16, c] 1 := by decide +kernel

theorem L1_21_17 : ∀ c : Fin 27, Fast.CertV ![21, 17, c] 1 := by decide +kernel

theorem L1_21_18 : ∀ c : Fin 27, Fast.CertV ![21, 18, c] 1 := by decide +kernel

theorem L1_21_19 : ∀ c : Fin 27, Fast.CertV ![21, 19, c] 1 := by decide +kernel

theorem L1_21_20 : ∀ c : Fin 27, Fast.CertV ![21, 20, c] 1 := by decide +kernel

theorem L1_21_21 : ∀ c : Fin 27, Fast.CertV ![21, 21, c] 1 := by decide +kernel

theorem L1_21_22 : ∀ c : Fin 27, Fast.CertV ![21, 22, c] 1 := by decide +kernel

theorem L1_21_23 : ∀ c : Fin 27, Fast.CertV ![21, 23, c] 1 := by decide +kernel

theorem L1_21_24 : ∀ c : Fin 27, Fast.CertV ![21, 24, c] 1 := by decide +kernel

theorem L1_21_25 : ∀ c : Fin 27, Fast.CertV ![21, 25, c] 1 := by decide +kernel

theorem L1_21_26 : ∀ c : Fin 27, Fast.CertV ![21, 26, c] 1 := by decide +kernel

theorem A1_21 : ∀ b c : Fin 27, Fast.CertV ![21, b, c] 1
  | ⟨0, _⟩ => L1_21_0
  | ⟨1, _⟩ => L1_21_1
  | ⟨2, _⟩ => L1_21_2
  | ⟨3, _⟩ => L1_21_3
  | ⟨4, _⟩ => L1_21_4
  | ⟨5, _⟩ => L1_21_5
  | ⟨6, _⟩ => L1_21_6
  | ⟨7, _⟩ => L1_21_7
  | ⟨8, _⟩ => L1_21_8
  | ⟨9, _⟩ => L1_21_9
  | ⟨10, _⟩ => L1_21_10
  | ⟨11, _⟩ => L1_21_11
  | ⟨12, _⟩ => L1_21_12
  | ⟨13, _⟩ => L1_21_13
  | ⟨14, _⟩ => L1_21_14
  | ⟨15, _⟩ => L1_21_15
  | ⟨16, _⟩ => L1_21_16
  | ⟨17, _⟩ => L1_21_17
  | ⟨18, _⟩ => L1_21_18
  | ⟨19, _⟩ => L1_21_19
  | ⟨20, _⟩ => L1_21_20
  | ⟨21, _⟩ => L1_21_21
  | ⟨22, _⟩ => L1_21_22
  | ⟨23, _⟩ => L1_21_23
  | ⟨24, _⟩ => L1_21_24
  | ⟨25, _⟩ => L1_21_25
  | ⟨26, _⟩ => L1_21_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_22_0 : ∀ c : Fin 27, Fast.CertV ![22, 0, c] 1 := by decide +kernel

theorem L1_22_1 : ∀ c : Fin 27, Fast.CertV ![22, 1, c] 1 := by decide +kernel

theorem L1_22_2 : ∀ c : Fin 27, Fast.CertV ![22, 2, c] 1 := by decide +kernel

theorem L1_22_3 : ∀ c : Fin 27, Fast.CertV ![22, 3, c] 1 := by decide +kernel

theorem L1_22_4 : ∀ c : Fin 27, Fast.CertV ![22, 4, c] 1 := by decide +kernel

theorem L1_22_5 : ∀ c : Fin 27, Fast.CertV ![22, 5, c] 1 := by decide +kernel

theorem L1_22_6 : ∀ c : Fin 27, Fast.CertV ![22, 6, c] 1 := by decide +kernel

theorem L1_22_7 : ∀ c : Fin 27, Fast.CertV ![22, 7, c] 1 := by decide +kernel

theorem L1_22_8 : ∀ c : Fin 27, Fast.CertV ![22, 8, c] 1 := by decide +kernel

theorem L1_22_9 : ∀ c : Fin 27, Fast.CertV ![22, 9, c] 1 := by decide +kernel

theorem L1_22_10 : ∀ c : Fin 27, Fast.CertV ![22, 10, c] 1 := by decide +kernel

theorem L1_22_11 : ∀ c : Fin 27, Fast.CertV ![22, 11, c] 1 := by decide +kernel

theorem L1_22_12 : ∀ c : Fin 27, Fast.CertV ![22, 12, c] 1 := by decide +kernel

theorem L1_22_13 : ∀ c : Fin 27, Fast.CertV ![22, 13, c] 1 := by decide +kernel

theorem L1_22_14 : ∀ c : Fin 27, Fast.CertV ![22, 14, c] 1 := by decide +kernel

theorem L1_22_15 : ∀ c : Fin 27, Fast.CertV ![22, 15, c] 1 := by decide +kernel

theorem L1_22_16 : ∀ c : Fin 27, Fast.CertV ![22, 16, c] 1 := by decide +kernel

theorem L1_22_17 : ∀ c : Fin 27, Fast.CertV ![22, 17, c] 1 := by decide +kernel

theorem L1_22_18 : ∀ c : Fin 27, Fast.CertV ![22, 18, c] 1 := by decide +kernel

theorem L1_22_19 : ∀ c : Fin 27, Fast.CertV ![22, 19, c] 1 := by decide +kernel

theorem L1_22_20 : ∀ c : Fin 27, Fast.CertV ![22, 20, c] 1 := by decide +kernel

theorem L1_22_21 : ∀ c : Fin 27, Fast.CertV ![22, 21, c] 1 := by decide +kernel

theorem L1_22_22 : ∀ c : Fin 27, Fast.CertV ![22, 22, c] 1 := by decide +kernel

theorem L1_22_23 : ∀ c : Fin 27, Fast.CertV ![22, 23, c] 1 := by decide +kernel

theorem L1_22_24 : ∀ c : Fin 27, Fast.CertV ![22, 24, c] 1 := by decide +kernel

theorem L1_22_25 : ∀ c : Fin 27, Fast.CertV ![22, 25, c] 1 := by decide +kernel

theorem L1_22_26 : ∀ c : Fin 27, Fast.CertV ![22, 26, c] 1 := by decide +kernel

theorem A1_22 : ∀ b c : Fin 27, Fast.CertV ![22, b, c] 1
  | ⟨0, _⟩ => L1_22_0
  | ⟨1, _⟩ => L1_22_1
  | ⟨2, _⟩ => L1_22_2
  | ⟨3, _⟩ => L1_22_3
  | ⟨4, _⟩ => L1_22_4
  | ⟨5, _⟩ => L1_22_5
  | ⟨6, _⟩ => L1_22_6
  | ⟨7, _⟩ => L1_22_7
  | ⟨8, _⟩ => L1_22_8
  | ⟨9, _⟩ => L1_22_9
  | ⟨10, _⟩ => L1_22_10
  | ⟨11, _⟩ => L1_22_11
  | ⟨12, _⟩ => L1_22_12
  | ⟨13, _⟩ => L1_22_13
  | ⟨14, _⟩ => L1_22_14
  | ⟨15, _⟩ => L1_22_15
  | ⟨16, _⟩ => L1_22_16
  | ⟨17, _⟩ => L1_22_17
  | ⟨18, _⟩ => L1_22_18
  | ⟨19, _⟩ => L1_22_19
  | ⟨20, _⟩ => L1_22_20
  | ⟨21, _⟩ => L1_22_21
  | ⟨22, _⟩ => L1_22_22
  | ⟨23, _⟩ => L1_22_23
  | ⟨24, _⟩ => L1_22_24
  | ⟨25, _⟩ => L1_22_25
  | ⟨26, _⟩ => L1_22_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_23_0 : ∀ c : Fin 27, Fast.CertV ![23, 0, c] 1 := by decide +kernel

theorem L1_23_1 : ∀ c : Fin 27, Fast.CertV ![23, 1, c] 1 := by decide +kernel

theorem L1_23_2 : ∀ c : Fin 27, Fast.CertV ![23, 2, c] 1 := by decide +kernel

theorem L1_23_3 : ∀ c : Fin 27, Fast.CertV ![23, 3, c] 1 := by decide +kernel

theorem L1_23_4 : ∀ c : Fin 27, Fast.CertV ![23, 4, c] 1 := by decide +kernel

theorem L1_23_5 : ∀ c : Fin 27, Fast.CertV ![23, 5, c] 1 := by decide +kernel

theorem L1_23_6 : ∀ c : Fin 27, Fast.CertV ![23, 6, c] 1 := by decide +kernel

theorem L1_23_7 : ∀ c : Fin 27, Fast.CertV ![23, 7, c] 1 := by decide +kernel

theorem L1_23_8 : ∀ c : Fin 27, Fast.CertV ![23, 8, c] 1 := by decide +kernel

theorem L1_23_9 : ∀ c : Fin 27, Fast.CertV ![23, 9, c] 1 := by decide +kernel

theorem L1_23_10 : ∀ c : Fin 27, Fast.CertV ![23, 10, c] 1 := by decide +kernel

theorem L1_23_11 : ∀ c : Fin 27, Fast.CertV ![23, 11, c] 1 := by decide +kernel

theorem L1_23_12 : ∀ c : Fin 27, Fast.CertV ![23, 12, c] 1 := by decide +kernel

theorem L1_23_13 : ∀ c : Fin 27, Fast.CertV ![23, 13, c] 1 := by decide +kernel

theorem L1_23_14 : ∀ c : Fin 27, Fast.CertV ![23, 14, c] 1 := by decide +kernel

theorem L1_23_15 : ∀ c : Fin 27, Fast.CertV ![23, 15, c] 1 := by decide +kernel

theorem L1_23_16 : ∀ c : Fin 27, Fast.CertV ![23, 16, c] 1 := by decide +kernel

theorem L1_23_17 : ∀ c : Fin 27, Fast.CertV ![23, 17, c] 1 := by decide +kernel

theorem L1_23_18 : ∀ c : Fin 27, Fast.CertV ![23, 18, c] 1 := by decide +kernel

theorem L1_23_19 : ∀ c : Fin 27, Fast.CertV ![23, 19, c] 1 := by decide +kernel

theorem L1_23_20 : ∀ c : Fin 27, Fast.CertV ![23, 20, c] 1 := by decide +kernel

theorem L1_23_21 : ∀ c : Fin 27, Fast.CertV ![23, 21, c] 1 := by decide +kernel

theorem L1_23_22 : ∀ c : Fin 27, Fast.CertV ![23, 22, c] 1 := by decide +kernel

theorem L1_23_23 : ∀ c : Fin 27, Fast.CertV ![23, 23, c] 1 := by decide +kernel

theorem L1_23_24 : ∀ c : Fin 27, Fast.CertV ![23, 24, c] 1 := by decide +kernel

theorem L1_23_25 : ∀ c : Fin 27, Fast.CertV ![23, 25, c] 1 := by decide +kernel

theorem L1_23_26 : ∀ c : Fin 27, Fast.CertV ![23, 26, c] 1 := by decide +kernel

theorem A1_23 : ∀ b c : Fin 27, Fast.CertV ![23, b, c] 1
  | ⟨0, _⟩ => L1_23_0
  | ⟨1, _⟩ => L1_23_1
  | ⟨2, _⟩ => L1_23_2
  | ⟨3, _⟩ => L1_23_3
  | ⟨4, _⟩ => L1_23_4
  | ⟨5, _⟩ => L1_23_5
  | ⟨6, _⟩ => L1_23_6
  | ⟨7, _⟩ => L1_23_7
  | ⟨8, _⟩ => L1_23_8
  | ⟨9, _⟩ => L1_23_9
  | ⟨10, _⟩ => L1_23_10
  | ⟨11, _⟩ => L1_23_11
  | ⟨12, _⟩ => L1_23_12
  | ⟨13, _⟩ => L1_23_13
  | ⟨14, _⟩ => L1_23_14
  | ⟨15, _⟩ => L1_23_15
  | ⟨16, _⟩ => L1_23_16
  | ⟨17, _⟩ => L1_23_17
  | ⟨18, _⟩ => L1_23_18
  | ⟨19, _⟩ => L1_23_19
  | ⟨20, _⟩ => L1_23_20
  | ⟨21, _⟩ => L1_23_21
  | ⟨22, _⟩ => L1_23_22
  | ⟨23, _⟩ => L1_23_23
  | ⟨24, _⟩ => L1_23_24
  | ⟨25, _⟩ => L1_23_25
  | ⟨26, _⟩ => L1_23_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_24_0 : ∀ c : Fin 27, Fast.CertV ![24, 0, c] 1 := by decide +kernel

theorem L1_24_1 : ∀ c : Fin 27, Fast.CertV ![24, 1, c] 1 := by decide +kernel

theorem L1_24_2 : ∀ c : Fin 27, Fast.CertV ![24, 2, c] 1 := by decide +kernel

theorem L1_24_3 : ∀ c : Fin 27, Fast.CertV ![24, 3, c] 1 := by decide +kernel

theorem L1_24_4 : ∀ c : Fin 27, Fast.CertV ![24, 4, c] 1 := by decide +kernel

theorem L1_24_5 : ∀ c : Fin 27, Fast.CertV ![24, 5, c] 1 := by decide +kernel

theorem L1_24_6 : ∀ c : Fin 27, Fast.CertV ![24, 6, c] 1 := by decide +kernel

theorem L1_24_7 : ∀ c : Fin 27, Fast.CertV ![24, 7, c] 1 := by decide +kernel

theorem L1_24_8 : ∀ c : Fin 27, Fast.CertV ![24, 8, c] 1 := by decide +kernel

theorem L1_24_9 : ∀ c : Fin 27, Fast.CertV ![24, 9, c] 1 := by decide +kernel

theorem L1_24_10 : ∀ c : Fin 27, Fast.CertV ![24, 10, c] 1 := by decide +kernel

theorem L1_24_11 : ∀ c : Fin 27, Fast.CertV ![24, 11, c] 1 := by decide +kernel

theorem L1_24_12 : ∀ c : Fin 27, Fast.CertV ![24, 12, c] 1 := by decide +kernel

theorem L1_24_13 : ∀ c : Fin 27, Fast.CertV ![24, 13, c] 1 := by decide +kernel

theorem L1_24_14 : ∀ c : Fin 27, Fast.CertV ![24, 14, c] 1 := by decide +kernel

theorem L1_24_15 : ∀ c : Fin 27, Fast.CertV ![24, 15, c] 1 := by decide +kernel

theorem L1_24_16 : ∀ c : Fin 27, Fast.CertV ![24, 16, c] 1 := by decide +kernel

theorem L1_24_17 : ∀ c : Fin 27, Fast.CertV ![24, 17, c] 1 := by decide +kernel

theorem L1_24_18 : ∀ c : Fin 27, Fast.CertV ![24, 18, c] 1 := by decide +kernel

theorem L1_24_19 : ∀ c : Fin 27, Fast.CertV ![24, 19, c] 1 := by decide +kernel

theorem L1_24_20 : ∀ c : Fin 27, Fast.CertV ![24, 20, c] 1 := by decide +kernel

theorem L1_24_21 : ∀ c : Fin 27, Fast.CertV ![24, 21, c] 1 := by decide +kernel

theorem L1_24_22 : ∀ c : Fin 27, Fast.CertV ![24, 22, c] 1 := by decide +kernel

theorem L1_24_23 : ∀ c : Fin 27, Fast.CertV ![24, 23, c] 1 := by decide +kernel

theorem L1_24_24 : ∀ c : Fin 27, Fast.CertV ![24, 24, c] 1 := by decide +kernel

theorem L1_24_25 : ∀ c : Fin 27, Fast.CertV ![24, 25, c] 1 := by decide +kernel

theorem L1_24_26 : ∀ c : Fin 27, Fast.CertV ![24, 26, c] 1 := by decide +kernel

theorem A1_24 : ∀ b c : Fin 27, Fast.CertV ![24, b, c] 1
  | ⟨0, _⟩ => L1_24_0
  | ⟨1, _⟩ => L1_24_1
  | ⟨2, _⟩ => L1_24_2
  | ⟨3, _⟩ => L1_24_3
  | ⟨4, _⟩ => L1_24_4
  | ⟨5, _⟩ => L1_24_5
  | ⟨6, _⟩ => L1_24_6
  | ⟨7, _⟩ => L1_24_7
  | ⟨8, _⟩ => L1_24_8
  | ⟨9, _⟩ => L1_24_9
  | ⟨10, _⟩ => L1_24_10
  | ⟨11, _⟩ => L1_24_11
  | ⟨12, _⟩ => L1_24_12
  | ⟨13, _⟩ => L1_24_13
  | ⟨14, _⟩ => L1_24_14
  | ⟨15, _⟩ => L1_24_15
  | ⟨16, _⟩ => L1_24_16
  | ⟨17, _⟩ => L1_24_17
  | ⟨18, _⟩ => L1_24_18
  | ⟨19, _⟩ => L1_24_19
  | ⟨20, _⟩ => L1_24_20
  | ⟨21, _⟩ => L1_24_21
  | ⟨22, _⟩ => L1_24_22
  | ⟨23, _⟩ => L1_24_23
  | ⟨24, _⟩ => L1_24_24
  | ⟨25, _⟩ => L1_24_25
  | ⟨26, _⟩ => L1_24_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_25_0 : ∀ c : Fin 27, Fast.CertV ![25, 0, c] 1 := by decide +kernel

theorem L1_25_1 : ∀ c : Fin 27, Fast.CertV ![25, 1, c] 1 := by decide +kernel

theorem L1_25_2 : ∀ c : Fin 27, Fast.CertV ![25, 2, c] 1 := by decide +kernel

theorem L1_25_3 : ∀ c : Fin 27, Fast.CertV ![25, 3, c] 1 := by decide +kernel

theorem L1_25_4 : ∀ c : Fin 27, Fast.CertV ![25, 4, c] 1 := by decide +kernel

theorem L1_25_5 : ∀ c : Fin 27, Fast.CertV ![25, 5, c] 1 := by decide +kernel

theorem L1_25_6 : ∀ c : Fin 27, Fast.CertV ![25, 6, c] 1 := by decide +kernel

theorem L1_25_7 : ∀ c : Fin 27, Fast.CertV ![25, 7, c] 1 := by decide +kernel

theorem L1_25_8 : ∀ c : Fin 27, Fast.CertV ![25, 8, c] 1 := by decide +kernel

theorem L1_25_9 : ∀ c : Fin 27, Fast.CertV ![25, 9, c] 1 := by decide +kernel

theorem L1_25_10 : ∀ c : Fin 27, Fast.CertV ![25, 10, c] 1 := by decide +kernel

theorem L1_25_11 : ∀ c : Fin 27, Fast.CertV ![25, 11, c] 1 := by decide +kernel

theorem L1_25_12 : ∀ c : Fin 27, Fast.CertV ![25, 12, c] 1 := by decide +kernel

theorem L1_25_13 : ∀ c : Fin 27, Fast.CertV ![25, 13, c] 1 := by decide +kernel

theorem L1_25_14 : ∀ c : Fin 27, Fast.CertV ![25, 14, c] 1 := by decide +kernel

theorem L1_25_15 : ∀ c : Fin 27, Fast.CertV ![25, 15, c] 1 := by decide +kernel

theorem L1_25_16 : ∀ c : Fin 27, Fast.CertV ![25, 16, c] 1 := by decide +kernel

theorem L1_25_17 : ∀ c : Fin 27, Fast.CertV ![25, 17, c] 1 := by decide +kernel

theorem L1_25_18 : ∀ c : Fin 27, Fast.CertV ![25, 18, c] 1 := by decide +kernel

theorem L1_25_19 : ∀ c : Fin 27, Fast.CertV ![25, 19, c] 1 := by decide +kernel

theorem L1_25_20 : ∀ c : Fin 27, Fast.CertV ![25, 20, c] 1 := by decide +kernel

theorem L1_25_21 : ∀ c : Fin 27, Fast.CertV ![25, 21, c] 1 := by decide +kernel

theorem L1_25_22 : ∀ c : Fin 27, Fast.CertV ![25, 22, c] 1 := by decide +kernel

theorem L1_25_23 : ∀ c : Fin 27, Fast.CertV ![25, 23, c] 1 := by decide +kernel

theorem L1_25_24 : ∀ c : Fin 27, Fast.CertV ![25, 24, c] 1 := by decide +kernel

theorem L1_25_25 : ∀ c : Fin 27, Fast.CertV ![25, 25, c] 1 := by decide +kernel

theorem L1_25_26 : ∀ c : Fin 27, Fast.CertV ![25, 26, c] 1 := by decide +kernel

theorem A1_25 : ∀ b c : Fin 27, Fast.CertV ![25, b, c] 1
  | ⟨0, _⟩ => L1_25_0
  | ⟨1, _⟩ => L1_25_1
  | ⟨2, _⟩ => L1_25_2
  | ⟨3, _⟩ => L1_25_3
  | ⟨4, _⟩ => L1_25_4
  | ⟨5, _⟩ => L1_25_5
  | ⟨6, _⟩ => L1_25_6
  | ⟨7, _⟩ => L1_25_7
  | ⟨8, _⟩ => L1_25_8
  | ⟨9, _⟩ => L1_25_9
  | ⟨10, _⟩ => L1_25_10
  | ⟨11, _⟩ => L1_25_11
  | ⟨12, _⟩ => L1_25_12
  | ⟨13, _⟩ => L1_25_13
  | ⟨14, _⟩ => L1_25_14
  | ⟨15, _⟩ => L1_25_15
  | ⟨16, _⟩ => L1_25_16
  | ⟨17, _⟩ => L1_25_17
  | ⟨18, _⟩ => L1_25_18
  | ⟨19, _⟩ => L1_25_19
  | ⟨20, _⟩ => L1_25_20
  | ⟨21, _⟩ => L1_25_21
  | ⟨22, _⟩ => L1_25_22
  | ⟨23, _⟩ => L1_25_23
  | ⟨24, _⟩ => L1_25_24
  | ⟨25, _⟩ => L1_25_25
  | ⟨26, _⟩ => L1_25_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L1_26_0 : ∀ c : Fin 27, Fast.CertV ![26, 0, c] 1 := by decide +kernel

theorem L1_26_1 : ∀ c : Fin 27, Fast.CertV ![26, 1, c] 1 := by decide +kernel

theorem L1_26_2 : ∀ c : Fin 27, Fast.CertV ![26, 2, c] 1 := by decide +kernel

theorem L1_26_3 : ∀ c : Fin 27, Fast.CertV ![26, 3, c] 1 := by decide +kernel

theorem L1_26_4 : ∀ c : Fin 27, Fast.CertV ![26, 4, c] 1 := by decide +kernel

theorem L1_26_5 : ∀ c : Fin 27, Fast.CertV ![26, 5, c] 1 := by decide +kernel

theorem L1_26_6 : ∀ c : Fin 27, Fast.CertV ![26, 6, c] 1 := by decide +kernel

theorem L1_26_7 : ∀ c : Fin 27, Fast.CertV ![26, 7, c] 1 := by decide +kernel

theorem L1_26_8 : ∀ c : Fin 27, Fast.CertV ![26, 8, c] 1 := by decide +kernel

theorem L1_26_9 : ∀ c : Fin 27, Fast.CertV ![26, 9, c] 1 := by decide +kernel

theorem L1_26_10 : ∀ c : Fin 27, Fast.CertV ![26, 10, c] 1 := by decide +kernel

theorem L1_26_11 : ∀ c : Fin 27, Fast.CertV ![26, 11, c] 1 := by decide +kernel

theorem L1_26_12 : ∀ c : Fin 27, Fast.CertV ![26, 12, c] 1 := by decide +kernel

theorem L1_26_13 : ∀ c : Fin 27, Fast.CertV ![26, 13, c] 1 := by decide +kernel

theorem L1_26_14 : ∀ c : Fin 27, Fast.CertV ![26, 14, c] 1 := by decide +kernel

theorem L1_26_15 : ∀ c : Fin 27, Fast.CertV ![26, 15, c] 1 := by decide +kernel

theorem L1_26_16 : ∀ c : Fin 27, Fast.CertV ![26, 16, c] 1 := by decide +kernel

theorem L1_26_17 : ∀ c : Fin 27, Fast.CertV ![26, 17, c] 1 := by decide +kernel

theorem L1_26_18 : ∀ c : Fin 27, Fast.CertV ![26, 18, c] 1 := by decide +kernel

theorem L1_26_19 : ∀ c : Fin 27, Fast.CertV ![26, 19, c] 1 := by decide +kernel

theorem L1_26_20 : ∀ c : Fin 27, Fast.CertV ![26, 20, c] 1 := by decide +kernel

theorem L1_26_21 : ∀ c : Fin 27, Fast.CertV ![26, 21, c] 1 := by decide +kernel

theorem L1_26_22 : ∀ c : Fin 27, Fast.CertV ![26, 22, c] 1 := by decide +kernel

theorem L1_26_23 : ∀ c : Fin 27, Fast.CertV ![26, 23, c] 1 := by decide +kernel

theorem L1_26_24 : ∀ c : Fin 27, Fast.CertV ![26, 24, c] 1 := by decide +kernel

theorem L1_26_25 : ∀ c : Fin 27, Fast.CertV ![26, 25, c] 1 := by decide +kernel

theorem L1_26_26 : ∀ c : Fin 27, Fast.CertV ![26, 26, c] 1 := by decide +kernel

theorem A1_26 : ∀ b c : Fin 27, Fast.CertV ![26, b, c] 1
  | ⟨0, _⟩ => L1_26_0
  | ⟨1, _⟩ => L1_26_1
  | ⟨2, _⟩ => L1_26_2
  | ⟨3, _⟩ => L1_26_3
  | ⟨4, _⟩ => L1_26_4
  | ⟨5, _⟩ => L1_26_5
  | ⟨6, _⟩ => L1_26_6
  | ⟨7, _⟩ => L1_26_7
  | ⟨8, _⟩ => L1_26_8
  | ⟨9, _⟩ => L1_26_9
  | ⟨10, _⟩ => L1_26_10
  | ⟨11, _⟩ => L1_26_11
  | ⟨12, _⟩ => L1_26_12
  | ⟨13, _⟩ => L1_26_13
  | ⟨14, _⟩ => L1_26_14
  | ⟨15, _⟩ => L1_26_15
  | ⟨16, _⟩ => L1_26_16
  | ⟨17, _⟩ => L1_26_17
  | ⟨18, _⟩ => L1_26_18
  | ⟨19, _⟩ => L1_26_19
  | ⟨20, _⟩ => L1_26_20
  | ⟨21, _⟩ => L1_26_21
  | ⟨22, _⟩ => L1_26_22
  | ⟨23, _⟩ => L1_26_23
  | ⟨24, _⟩ => L1_26_24
  | ⟨25, _⟩ => L1_26_25
  | ⟨26, _⟩ => L1_26_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

end E1Cert.Table
