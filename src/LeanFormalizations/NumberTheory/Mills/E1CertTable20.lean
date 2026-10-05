/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.E1CertCore

/-! Kernel table for `E1Cert.cert_all`: `t = 2`, `a ∈ [0, 9)`. -/

namespace E1Cert.Table

set_option maxRecDepth 100000

theorem L2_0_0 : ∀ c : Fin 27, Fast.CertV ![0, 0, c] 2 := by decide +kernel

theorem L2_0_1 : ∀ c : Fin 27, Fast.CertV ![0, 1, c] 2 := by decide +kernel

theorem L2_0_2 : ∀ c : Fin 27, Fast.CertV ![0, 2, c] 2 := by decide +kernel

theorem L2_0_3 : ∀ c : Fin 27, Fast.CertV ![0, 3, c] 2 := by decide +kernel

theorem L2_0_4 : ∀ c : Fin 27, Fast.CertV ![0, 4, c] 2 := by decide +kernel

theorem L2_0_5 : ∀ c : Fin 27, Fast.CertV ![0, 5, c] 2 := by decide +kernel

theorem L2_0_6 : ∀ c : Fin 27, Fast.CertV ![0, 6, c] 2 := by decide +kernel

theorem L2_0_7 : ∀ c : Fin 27, Fast.CertV ![0, 7, c] 2 := by decide +kernel

theorem L2_0_8 : ∀ c : Fin 27, Fast.CertV ![0, 8, c] 2 := by decide +kernel

theorem L2_0_9 : ∀ c : Fin 27, Fast.CertV ![0, 9, c] 2 := by decide +kernel

theorem L2_0_10 : ∀ c : Fin 27, Fast.CertV ![0, 10, c] 2 := by decide +kernel

theorem L2_0_11 : ∀ c : Fin 27, Fast.CertV ![0, 11, c] 2 := by decide +kernel

theorem L2_0_12 : ∀ c : Fin 27, Fast.CertV ![0, 12, c] 2 := by decide +kernel

theorem L2_0_13 : ∀ c : Fin 27, Fast.CertV ![0, 13, c] 2 := by decide +kernel

theorem L2_0_14 : ∀ c : Fin 27, Fast.CertV ![0, 14, c] 2 := by decide +kernel

theorem L2_0_15 : ∀ c : Fin 27, Fast.CertV ![0, 15, c] 2 := by decide +kernel

theorem L2_0_16 : ∀ c : Fin 27, Fast.CertV ![0, 16, c] 2 := by decide +kernel

theorem L2_0_17 : ∀ c : Fin 27, Fast.CertV ![0, 17, c] 2 := by decide +kernel

theorem L2_0_18 : ∀ c : Fin 27, Fast.CertV ![0, 18, c] 2 := by decide +kernel

theorem L2_0_19 : ∀ c : Fin 27, Fast.CertV ![0, 19, c] 2 := by decide +kernel

theorem L2_0_20 : ∀ c : Fin 27, Fast.CertV ![0, 20, c] 2 := by decide +kernel

theorem L2_0_21 : ∀ c : Fin 27, Fast.CertV ![0, 21, c] 2 := by decide +kernel

theorem L2_0_22 : ∀ c : Fin 27, Fast.CertV ![0, 22, c] 2 := by decide +kernel

theorem L2_0_23 : ∀ c : Fin 27, Fast.CertV ![0, 23, c] 2 := by decide +kernel

theorem L2_0_24 : ∀ c : Fin 27, Fast.CertV ![0, 24, c] 2 := by decide +kernel

theorem L2_0_25 : ∀ c : Fin 27, Fast.CertV ![0, 25, c] 2 := by decide +kernel

theorem L2_0_26 : ∀ c : Fin 27, Fast.CertV ![0, 26, c] 2 := by decide +kernel

theorem A2_0 : ∀ b c : Fin 27, Fast.CertV ![0, b, c] 2
  | ⟨0, _⟩ => L2_0_0
  | ⟨1, _⟩ => L2_0_1
  | ⟨2, _⟩ => L2_0_2
  | ⟨3, _⟩ => L2_0_3
  | ⟨4, _⟩ => L2_0_4
  | ⟨5, _⟩ => L2_0_5
  | ⟨6, _⟩ => L2_0_6
  | ⟨7, _⟩ => L2_0_7
  | ⟨8, _⟩ => L2_0_8
  | ⟨9, _⟩ => L2_0_9
  | ⟨10, _⟩ => L2_0_10
  | ⟨11, _⟩ => L2_0_11
  | ⟨12, _⟩ => L2_0_12
  | ⟨13, _⟩ => L2_0_13
  | ⟨14, _⟩ => L2_0_14
  | ⟨15, _⟩ => L2_0_15
  | ⟨16, _⟩ => L2_0_16
  | ⟨17, _⟩ => L2_0_17
  | ⟨18, _⟩ => L2_0_18
  | ⟨19, _⟩ => L2_0_19
  | ⟨20, _⟩ => L2_0_20
  | ⟨21, _⟩ => L2_0_21
  | ⟨22, _⟩ => L2_0_22
  | ⟨23, _⟩ => L2_0_23
  | ⟨24, _⟩ => L2_0_24
  | ⟨25, _⟩ => L2_0_25
  | ⟨26, _⟩ => L2_0_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_1_0 : ∀ c : Fin 27, Fast.CertV ![1, 0, c] 2 := by decide +kernel

theorem L2_1_1 : ∀ c : Fin 27, Fast.CertV ![1, 1, c] 2 := by decide +kernel

theorem L2_1_2 : ∀ c : Fin 27, Fast.CertV ![1, 2, c] 2 := by decide +kernel

theorem L2_1_3 : ∀ c : Fin 27, Fast.CertV ![1, 3, c] 2 := by decide +kernel

theorem L2_1_4 : ∀ c : Fin 27, Fast.CertV ![1, 4, c] 2 := by decide +kernel

theorem L2_1_5 : ∀ c : Fin 27, Fast.CertV ![1, 5, c] 2 := by decide +kernel

theorem L2_1_6 : ∀ c : Fin 27, Fast.CertV ![1, 6, c] 2 := by decide +kernel

theorem L2_1_7 : ∀ c : Fin 27, Fast.CertV ![1, 7, c] 2 := by decide +kernel

theorem L2_1_8 : ∀ c : Fin 27, Fast.CertV ![1, 8, c] 2 := by decide +kernel

theorem L2_1_9 : ∀ c : Fin 27, Fast.CertV ![1, 9, c] 2 := by decide +kernel

theorem L2_1_10 : ∀ c : Fin 27, Fast.CertV ![1, 10, c] 2 := by decide +kernel

theorem L2_1_11 : ∀ c : Fin 27, Fast.CertV ![1, 11, c] 2 := by decide +kernel

theorem L2_1_12 : ∀ c : Fin 27, Fast.CertV ![1, 12, c] 2 := by decide +kernel

theorem L2_1_13 : ∀ c : Fin 27, Fast.CertV ![1, 13, c] 2 := by decide +kernel

theorem L2_1_14 : ∀ c : Fin 27, Fast.CertV ![1, 14, c] 2 := by decide +kernel

theorem L2_1_15 : ∀ c : Fin 27, Fast.CertV ![1, 15, c] 2 := by decide +kernel

theorem L2_1_16 : ∀ c : Fin 27, Fast.CertV ![1, 16, c] 2 := by decide +kernel

theorem L2_1_17 : ∀ c : Fin 27, Fast.CertV ![1, 17, c] 2 := by decide +kernel

theorem L2_1_18 : ∀ c : Fin 27, Fast.CertV ![1, 18, c] 2 := by decide +kernel

theorem L2_1_19 : ∀ c : Fin 27, Fast.CertV ![1, 19, c] 2 := by decide +kernel

theorem L2_1_20 : ∀ c : Fin 27, Fast.CertV ![1, 20, c] 2 := by decide +kernel

theorem L2_1_21 : ∀ c : Fin 27, Fast.CertV ![1, 21, c] 2 := by decide +kernel

theorem L2_1_22 : ∀ c : Fin 27, Fast.CertV ![1, 22, c] 2 := by decide +kernel

theorem L2_1_23 : ∀ c : Fin 27, Fast.CertV ![1, 23, c] 2 := by decide +kernel

theorem L2_1_24 : ∀ c : Fin 27, Fast.CertV ![1, 24, c] 2 := by decide +kernel

theorem L2_1_25 : ∀ c : Fin 27, Fast.CertV ![1, 25, c] 2 := by decide +kernel

theorem L2_1_26 : ∀ c : Fin 27, Fast.CertV ![1, 26, c] 2 := by decide +kernel

theorem A2_1 : ∀ b c : Fin 27, Fast.CertV ![1, b, c] 2
  | ⟨0, _⟩ => L2_1_0
  | ⟨1, _⟩ => L2_1_1
  | ⟨2, _⟩ => L2_1_2
  | ⟨3, _⟩ => L2_1_3
  | ⟨4, _⟩ => L2_1_4
  | ⟨5, _⟩ => L2_1_5
  | ⟨6, _⟩ => L2_1_6
  | ⟨7, _⟩ => L2_1_7
  | ⟨8, _⟩ => L2_1_8
  | ⟨9, _⟩ => L2_1_9
  | ⟨10, _⟩ => L2_1_10
  | ⟨11, _⟩ => L2_1_11
  | ⟨12, _⟩ => L2_1_12
  | ⟨13, _⟩ => L2_1_13
  | ⟨14, _⟩ => L2_1_14
  | ⟨15, _⟩ => L2_1_15
  | ⟨16, _⟩ => L2_1_16
  | ⟨17, _⟩ => L2_1_17
  | ⟨18, _⟩ => L2_1_18
  | ⟨19, _⟩ => L2_1_19
  | ⟨20, _⟩ => L2_1_20
  | ⟨21, _⟩ => L2_1_21
  | ⟨22, _⟩ => L2_1_22
  | ⟨23, _⟩ => L2_1_23
  | ⟨24, _⟩ => L2_1_24
  | ⟨25, _⟩ => L2_1_25
  | ⟨26, _⟩ => L2_1_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_2_0 : ∀ c : Fin 27, Fast.CertV ![2, 0, c] 2 := by decide +kernel

theorem L2_2_1 : ∀ c : Fin 27, Fast.CertV ![2, 1, c] 2 := by decide +kernel

theorem L2_2_2 : ∀ c : Fin 27, Fast.CertV ![2, 2, c] 2 := by decide +kernel

theorem L2_2_3 : ∀ c : Fin 27, Fast.CertV ![2, 3, c] 2 := by decide +kernel

theorem L2_2_4 : ∀ c : Fin 27, Fast.CertV ![2, 4, c] 2 := by decide +kernel

theorem L2_2_5 : ∀ c : Fin 27, Fast.CertV ![2, 5, c] 2 := by decide +kernel

theorem L2_2_6 : ∀ c : Fin 27, Fast.CertV ![2, 6, c] 2 := by decide +kernel

theorem L2_2_7 : ∀ c : Fin 27, Fast.CertV ![2, 7, c] 2 := by decide +kernel

theorem L2_2_8 : ∀ c : Fin 27, Fast.CertV ![2, 8, c] 2 := by decide +kernel

theorem L2_2_9 : ∀ c : Fin 27, Fast.CertV ![2, 9, c] 2 := by decide +kernel

theorem L2_2_10 : ∀ c : Fin 27, Fast.CertV ![2, 10, c] 2 := by decide +kernel

theorem L2_2_11 : ∀ c : Fin 27, Fast.CertV ![2, 11, c] 2 := by decide +kernel

theorem L2_2_12 : ∀ c : Fin 27, Fast.CertV ![2, 12, c] 2 := by decide +kernel

theorem L2_2_13 : ∀ c : Fin 27, Fast.CertV ![2, 13, c] 2 := by decide +kernel

theorem L2_2_14 : ∀ c : Fin 27, Fast.CertV ![2, 14, c] 2 := by decide +kernel

theorem L2_2_15 : ∀ c : Fin 27, Fast.CertV ![2, 15, c] 2 := by decide +kernel

theorem L2_2_16 : ∀ c : Fin 27, Fast.CertV ![2, 16, c] 2 := by decide +kernel

theorem L2_2_17 : ∀ c : Fin 27, Fast.CertV ![2, 17, c] 2 := by decide +kernel

theorem L2_2_18 : ∀ c : Fin 27, Fast.CertV ![2, 18, c] 2 := by decide +kernel

theorem L2_2_19 : ∀ c : Fin 27, Fast.CertV ![2, 19, c] 2 := by decide +kernel

theorem L2_2_20 : ∀ c : Fin 27, Fast.CertV ![2, 20, c] 2 := by decide +kernel

theorem L2_2_21 : ∀ c : Fin 27, Fast.CertV ![2, 21, c] 2 := by decide +kernel

theorem L2_2_22 : ∀ c : Fin 27, Fast.CertV ![2, 22, c] 2 := by decide +kernel

theorem L2_2_23 : ∀ c : Fin 27, Fast.CertV ![2, 23, c] 2 := by decide +kernel

theorem L2_2_24 : ∀ c : Fin 27, Fast.CertV ![2, 24, c] 2 := by decide +kernel

theorem L2_2_25 : ∀ c : Fin 27, Fast.CertV ![2, 25, c] 2 := by decide +kernel

theorem L2_2_26 : ∀ c : Fin 27, Fast.CertV ![2, 26, c] 2 := by decide +kernel

theorem A2_2 : ∀ b c : Fin 27, Fast.CertV ![2, b, c] 2
  | ⟨0, _⟩ => L2_2_0
  | ⟨1, _⟩ => L2_2_1
  | ⟨2, _⟩ => L2_2_2
  | ⟨3, _⟩ => L2_2_3
  | ⟨4, _⟩ => L2_2_4
  | ⟨5, _⟩ => L2_2_5
  | ⟨6, _⟩ => L2_2_6
  | ⟨7, _⟩ => L2_2_7
  | ⟨8, _⟩ => L2_2_8
  | ⟨9, _⟩ => L2_2_9
  | ⟨10, _⟩ => L2_2_10
  | ⟨11, _⟩ => L2_2_11
  | ⟨12, _⟩ => L2_2_12
  | ⟨13, _⟩ => L2_2_13
  | ⟨14, _⟩ => L2_2_14
  | ⟨15, _⟩ => L2_2_15
  | ⟨16, _⟩ => L2_2_16
  | ⟨17, _⟩ => L2_2_17
  | ⟨18, _⟩ => L2_2_18
  | ⟨19, _⟩ => L2_2_19
  | ⟨20, _⟩ => L2_2_20
  | ⟨21, _⟩ => L2_2_21
  | ⟨22, _⟩ => L2_2_22
  | ⟨23, _⟩ => L2_2_23
  | ⟨24, _⟩ => L2_2_24
  | ⟨25, _⟩ => L2_2_25
  | ⟨26, _⟩ => L2_2_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_3_0 : ∀ c : Fin 27, Fast.CertV ![3, 0, c] 2 := by decide +kernel

theorem L2_3_1 : ∀ c : Fin 27, Fast.CertV ![3, 1, c] 2 := by decide +kernel

theorem L2_3_2 : ∀ c : Fin 27, Fast.CertV ![3, 2, c] 2 := by decide +kernel

theorem L2_3_3 : ∀ c : Fin 27, Fast.CertV ![3, 3, c] 2 := by decide +kernel

theorem L2_3_4 : ∀ c : Fin 27, Fast.CertV ![3, 4, c] 2 := by decide +kernel

theorem L2_3_5 : ∀ c : Fin 27, Fast.CertV ![3, 5, c] 2 := by decide +kernel

theorem L2_3_6 : ∀ c : Fin 27, Fast.CertV ![3, 6, c] 2 := by decide +kernel

theorem L2_3_7 : ∀ c : Fin 27, Fast.CertV ![3, 7, c] 2 := by decide +kernel

theorem L2_3_8 : ∀ c : Fin 27, Fast.CertV ![3, 8, c] 2 := by decide +kernel

theorem L2_3_9 : ∀ c : Fin 27, Fast.CertV ![3, 9, c] 2 := by decide +kernel

theorem L2_3_10 : ∀ c : Fin 27, Fast.CertV ![3, 10, c] 2 := by decide +kernel

theorem L2_3_11 : ∀ c : Fin 27, Fast.CertV ![3, 11, c] 2 := by decide +kernel

theorem L2_3_12 : ∀ c : Fin 27, Fast.CertV ![3, 12, c] 2 := by decide +kernel

theorem L2_3_13 : ∀ c : Fin 27, Fast.CertV ![3, 13, c] 2 := by decide +kernel

theorem L2_3_14 : ∀ c : Fin 27, Fast.CertV ![3, 14, c] 2 := by decide +kernel

theorem L2_3_15 : ∀ c : Fin 27, Fast.CertV ![3, 15, c] 2 := by decide +kernel

theorem L2_3_16 : ∀ c : Fin 27, Fast.CertV ![3, 16, c] 2 := by decide +kernel

theorem L2_3_17 : ∀ c : Fin 27, Fast.CertV ![3, 17, c] 2 := by decide +kernel

theorem L2_3_18 : ∀ c : Fin 27, Fast.CertV ![3, 18, c] 2 := by decide +kernel

theorem L2_3_19 : ∀ c : Fin 27, Fast.CertV ![3, 19, c] 2 := by decide +kernel

theorem L2_3_20 : ∀ c : Fin 27, Fast.CertV ![3, 20, c] 2 := by decide +kernel

theorem L2_3_21 : ∀ c : Fin 27, Fast.CertV ![3, 21, c] 2 := by decide +kernel

theorem L2_3_22 : ∀ c : Fin 27, Fast.CertV ![3, 22, c] 2 := by decide +kernel

theorem L2_3_23 : ∀ c : Fin 27, Fast.CertV ![3, 23, c] 2 := by decide +kernel

theorem L2_3_24 : ∀ c : Fin 27, Fast.CertV ![3, 24, c] 2 := by decide +kernel

theorem L2_3_25 : ∀ c : Fin 27, Fast.CertV ![3, 25, c] 2 := by decide +kernel

theorem L2_3_26 : ∀ c : Fin 27, Fast.CertV ![3, 26, c] 2 := by decide +kernel

theorem A2_3 : ∀ b c : Fin 27, Fast.CertV ![3, b, c] 2
  | ⟨0, _⟩ => L2_3_0
  | ⟨1, _⟩ => L2_3_1
  | ⟨2, _⟩ => L2_3_2
  | ⟨3, _⟩ => L2_3_3
  | ⟨4, _⟩ => L2_3_4
  | ⟨5, _⟩ => L2_3_5
  | ⟨6, _⟩ => L2_3_6
  | ⟨7, _⟩ => L2_3_7
  | ⟨8, _⟩ => L2_3_8
  | ⟨9, _⟩ => L2_3_9
  | ⟨10, _⟩ => L2_3_10
  | ⟨11, _⟩ => L2_3_11
  | ⟨12, _⟩ => L2_3_12
  | ⟨13, _⟩ => L2_3_13
  | ⟨14, _⟩ => L2_3_14
  | ⟨15, _⟩ => L2_3_15
  | ⟨16, _⟩ => L2_3_16
  | ⟨17, _⟩ => L2_3_17
  | ⟨18, _⟩ => L2_3_18
  | ⟨19, _⟩ => L2_3_19
  | ⟨20, _⟩ => L2_3_20
  | ⟨21, _⟩ => L2_3_21
  | ⟨22, _⟩ => L2_3_22
  | ⟨23, _⟩ => L2_3_23
  | ⟨24, _⟩ => L2_3_24
  | ⟨25, _⟩ => L2_3_25
  | ⟨26, _⟩ => L2_3_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_4_0 : ∀ c : Fin 27, Fast.CertV ![4, 0, c] 2 := by decide +kernel

theorem L2_4_1 : ∀ c : Fin 27, Fast.CertV ![4, 1, c] 2 := by decide +kernel

theorem L2_4_2 : ∀ c : Fin 27, Fast.CertV ![4, 2, c] 2 := by decide +kernel

theorem L2_4_3 : ∀ c : Fin 27, Fast.CertV ![4, 3, c] 2 := by decide +kernel

theorem L2_4_4 : ∀ c : Fin 27, Fast.CertV ![4, 4, c] 2 := by decide +kernel

theorem L2_4_5 : ∀ c : Fin 27, Fast.CertV ![4, 5, c] 2 := by decide +kernel

theorem L2_4_6 : ∀ c : Fin 27, Fast.CertV ![4, 6, c] 2 := by decide +kernel

theorem L2_4_7 : ∀ c : Fin 27, Fast.CertV ![4, 7, c] 2 := by decide +kernel

theorem L2_4_8 : ∀ c : Fin 27, Fast.CertV ![4, 8, c] 2 := by decide +kernel

theorem L2_4_9 : ∀ c : Fin 27, Fast.CertV ![4, 9, c] 2 := by decide +kernel

theorem L2_4_10 : ∀ c : Fin 27, Fast.CertV ![4, 10, c] 2 := by decide +kernel

theorem L2_4_11 : ∀ c : Fin 27, Fast.CertV ![4, 11, c] 2 := by decide +kernel

theorem L2_4_12 : ∀ c : Fin 27, Fast.CertV ![4, 12, c] 2 := by decide +kernel

theorem L2_4_13 : ∀ c : Fin 27, Fast.CertV ![4, 13, c] 2 := by decide +kernel

theorem L2_4_14 : ∀ c : Fin 27, Fast.CertV ![4, 14, c] 2 := by decide +kernel

theorem L2_4_15 : ∀ c : Fin 27, Fast.CertV ![4, 15, c] 2 := by decide +kernel

theorem L2_4_16 : ∀ c : Fin 27, Fast.CertV ![4, 16, c] 2 := by decide +kernel

theorem L2_4_17 : ∀ c : Fin 27, Fast.CertV ![4, 17, c] 2 := by decide +kernel

theorem L2_4_18 : ∀ c : Fin 27, Fast.CertV ![4, 18, c] 2 := by decide +kernel

theorem L2_4_19 : ∀ c : Fin 27, Fast.CertV ![4, 19, c] 2 := by decide +kernel

theorem L2_4_20 : ∀ c : Fin 27, Fast.CertV ![4, 20, c] 2 := by decide +kernel

theorem L2_4_21 : ∀ c : Fin 27, Fast.CertV ![4, 21, c] 2 := by decide +kernel

theorem L2_4_22 : ∀ c : Fin 27, Fast.CertV ![4, 22, c] 2 := by decide +kernel

theorem L2_4_23 : ∀ c : Fin 27, Fast.CertV ![4, 23, c] 2 := by decide +kernel

theorem L2_4_24 : ∀ c : Fin 27, Fast.CertV ![4, 24, c] 2 := by decide +kernel

theorem L2_4_25 : ∀ c : Fin 27, Fast.CertV ![4, 25, c] 2 := by decide +kernel

theorem L2_4_26 : ∀ c : Fin 27, Fast.CertV ![4, 26, c] 2 := by decide +kernel

theorem A2_4 : ∀ b c : Fin 27, Fast.CertV ![4, b, c] 2
  | ⟨0, _⟩ => L2_4_0
  | ⟨1, _⟩ => L2_4_1
  | ⟨2, _⟩ => L2_4_2
  | ⟨3, _⟩ => L2_4_3
  | ⟨4, _⟩ => L2_4_4
  | ⟨5, _⟩ => L2_4_5
  | ⟨6, _⟩ => L2_4_6
  | ⟨7, _⟩ => L2_4_7
  | ⟨8, _⟩ => L2_4_8
  | ⟨9, _⟩ => L2_4_9
  | ⟨10, _⟩ => L2_4_10
  | ⟨11, _⟩ => L2_4_11
  | ⟨12, _⟩ => L2_4_12
  | ⟨13, _⟩ => L2_4_13
  | ⟨14, _⟩ => L2_4_14
  | ⟨15, _⟩ => L2_4_15
  | ⟨16, _⟩ => L2_4_16
  | ⟨17, _⟩ => L2_4_17
  | ⟨18, _⟩ => L2_4_18
  | ⟨19, _⟩ => L2_4_19
  | ⟨20, _⟩ => L2_4_20
  | ⟨21, _⟩ => L2_4_21
  | ⟨22, _⟩ => L2_4_22
  | ⟨23, _⟩ => L2_4_23
  | ⟨24, _⟩ => L2_4_24
  | ⟨25, _⟩ => L2_4_25
  | ⟨26, _⟩ => L2_4_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_5_0 : ∀ c : Fin 27, Fast.CertV ![5, 0, c] 2 := by decide +kernel

theorem L2_5_1 : ∀ c : Fin 27, Fast.CertV ![5, 1, c] 2 := by decide +kernel

theorem L2_5_2 : ∀ c : Fin 27, Fast.CertV ![5, 2, c] 2 := by decide +kernel

theorem L2_5_3 : ∀ c : Fin 27, Fast.CertV ![5, 3, c] 2 := by decide +kernel

theorem L2_5_4 : ∀ c : Fin 27, Fast.CertV ![5, 4, c] 2 := by decide +kernel

theorem L2_5_5 : ∀ c : Fin 27, Fast.CertV ![5, 5, c] 2 := by decide +kernel

theorem L2_5_6 : ∀ c : Fin 27, Fast.CertV ![5, 6, c] 2 := by decide +kernel

theorem L2_5_7 : ∀ c : Fin 27, Fast.CertV ![5, 7, c] 2 := by decide +kernel

theorem L2_5_8 : ∀ c : Fin 27, Fast.CertV ![5, 8, c] 2 := by decide +kernel

theorem L2_5_9 : ∀ c : Fin 27, Fast.CertV ![5, 9, c] 2 := by decide +kernel

theorem L2_5_10 : ∀ c : Fin 27, Fast.CertV ![5, 10, c] 2 := by decide +kernel

theorem L2_5_11 : ∀ c : Fin 27, Fast.CertV ![5, 11, c] 2 := by decide +kernel

theorem L2_5_12 : ∀ c : Fin 27, Fast.CertV ![5, 12, c] 2 := by decide +kernel

theorem L2_5_13 : ∀ c : Fin 27, Fast.CertV ![5, 13, c] 2 := by decide +kernel

theorem L2_5_14 : ∀ c : Fin 27, Fast.CertV ![5, 14, c] 2 := by decide +kernel

theorem L2_5_15 : ∀ c : Fin 27, Fast.CertV ![5, 15, c] 2 := by decide +kernel

theorem L2_5_16 : ∀ c : Fin 27, Fast.CertV ![5, 16, c] 2 := by decide +kernel

theorem L2_5_17 : ∀ c : Fin 27, Fast.CertV ![5, 17, c] 2 := by decide +kernel

theorem L2_5_18 : ∀ c : Fin 27, Fast.CertV ![5, 18, c] 2 := by decide +kernel

theorem L2_5_19 : ∀ c : Fin 27, Fast.CertV ![5, 19, c] 2 := by decide +kernel

theorem L2_5_20 : ∀ c : Fin 27, Fast.CertV ![5, 20, c] 2 := by decide +kernel

theorem L2_5_21 : ∀ c : Fin 27, Fast.CertV ![5, 21, c] 2 := by decide +kernel

theorem L2_5_22 : ∀ c : Fin 27, Fast.CertV ![5, 22, c] 2 := by decide +kernel

theorem L2_5_23 : ∀ c : Fin 27, Fast.CertV ![5, 23, c] 2 := by decide +kernel

theorem L2_5_24 : ∀ c : Fin 27, Fast.CertV ![5, 24, c] 2 := by decide +kernel

theorem L2_5_25 : ∀ c : Fin 27, Fast.CertV ![5, 25, c] 2 := by decide +kernel

theorem L2_5_26 : ∀ c : Fin 27, Fast.CertV ![5, 26, c] 2 := by decide +kernel

theorem A2_5 : ∀ b c : Fin 27, Fast.CertV ![5, b, c] 2
  | ⟨0, _⟩ => L2_5_0
  | ⟨1, _⟩ => L2_5_1
  | ⟨2, _⟩ => L2_5_2
  | ⟨3, _⟩ => L2_5_3
  | ⟨4, _⟩ => L2_5_4
  | ⟨5, _⟩ => L2_5_5
  | ⟨6, _⟩ => L2_5_6
  | ⟨7, _⟩ => L2_5_7
  | ⟨8, _⟩ => L2_5_8
  | ⟨9, _⟩ => L2_5_9
  | ⟨10, _⟩ => L2_5_10
  | ⟨11, _⟩ => L2_5_11
  | ⟨12, _⟩ => L2_5_12
  | ⟨13, _⟩ => L2_5_13
  | ⟨14, _⟩ => L2_5_14
  | ⟨15, _⟩ => L2_5_15
  | ⟨16, _⟩ => L2_5_16
  | ⟨17, _⟩ => L2_5_17
  | ⟨18, _⟩ => L2_5_18
  | ⟨19, _⟩ => L2_5_19
  | ⟨20, _⟩ => L2_5_20
  | ⟨21, _⟩ => L2_5_21
  | ⟨22, _⟩ => L2_5_22
  | ⟨23, _⟩ => L2_5_23
  | ⟨24, _⟩ => L2_5_24
  | ⟨25, _⟩ => L2_5_25
  | ⟨26, _⟩ => L2_5_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_6_0 : ∀ c : Fin 27, Fast.CertV ![6, 0, c] 2 := by decide +kernel

theorem L2_6_1 : ∀ c : Fin 27, Fast.CertV ![6, 1, c] 2 := by decide +kernel

theorem L2_6_2 : ∀ c : Fin 27, Fast.CertV ![6, 2, c] 2 := by decide +kernel

theorem L2_6_3 : ∀ c : Fin 27, Fast.CertV ![6, 3, c] 2 := by decide +kernel

theorem L2_6_4 : ∀ c : Fin 27, Fast.CertV ![6, 4, c] 2 := by decide +kernel

theorem L2_6_5 : ∀ c : Fin 27, Fast.CertV ![6, 5, c] 2 := by decide +kernel

theorem L2_6_6 : ∀ c : Fin 27, Fast.CertV ![6, 6, c] 2 := by decide +kernel

theorem L2_6_7 : ∀ c : Fin 27, Fast.CertV ![6, 7, c] 2 := by decide +kernel

theorem L2_6_8 : ∀ c : Fin 27, Fast.CertV ![6, 8, c] 2 := by decide +kernel

theorem L2_6_9 : ∀ c : Fin 27, Fast.CertV ![6, 9, c] 2 := by decide +kernel

theorem L2_6_10 : ∀ c : Fin 27, Fast.CertV ![6, 10, c] 2 := by decide +kernel

theorem L2_6_11 : ∀ c : Fin 27, Fast.CertV ![6, 11, c] 2 := by decide +kernel

theorem L2_6_12 : ∀ c : Fin 27, Fast.CertV ![6, 12, c] 2 := by decide +kernel

theorem L2_6_13 : ∀ c : Fin 27, Fast.CertV ![6, 13, c] 2 := by decide +kernel

theorem L2_6_14 : ∀ c : Fin 27, Fast.CertV ![6, 14, c] 2 := by decide +kernel

theorem L2_6_15 : ∀ c : Fin 27, Fast.CertV ![6, 15, c] 2 := by decide +kernel

theorem L2_6_16 : ∀ c : Fin 27, Fast.CertV ![6, 16, c] 2 := by decide +kernel

theorem L2_6_17 : ∀ c : Fin 27, Fast.CertV ![6, 17, c] 2 := by decide +kernel

theorem L2_6_18 : ∀ c : Fin 27, Fast.CertV ![6, 18, c] 2 := by decide +kernel

theorem L2_6_19 : ∀ c : Fin 27, Fast.CertV ![6, 19, c] 2 := by decide +kernel

theorem L2_6_20 : ∀ c : Fin 27, Fast.CertV ![6, 20, c] 2 := by decide +kernel

theorem L2_6_21 : ∀ c : Fin 27, Fast.CertV ![6, 21, c] 2 := by decide +kernel

theorem L2_6_22 : ∀ c : Fin 27, Fast.CertV ![6, 22, c] 2 := by decide +kernel

theorem L2_6_23 : ∀ c : Fin 27, Fast.CertV ![6, 23, c] 2 := by decide +kernel

theorem L2_6_24 : ∀ c : Fin 27, Fast.CertV ![6, 24, c] 2 := by decide +kernel

theorem L2_6_25 : ∀ c : Fin 27, Fast.CertV ![6, 25, c] 2 := by decide +kernel

theorem L2_6_26 : ∀ c : Fin 27, Fast.CertV ![6, 26, c] 2 := by decide +kernel

theorem A2_6 : ∀ b c : Fin 27, Fast.CertV ![6, b, c] 2
  | ⟨0, _⟩ => L2_6_0
  | ⟨1, _⟩ => L2_6_1
  | ⟨2, _⟩ => L2_6_2
  | ⟨3, _⟩ => L2_6_3
  | ⟨4, _⟩ => L2_6_4
  | ⟨5, _⟩ => L2_6_5
  | ⟨6, _⟩ => L2_6_6
  | ⟨7, _⟩ => L2_6_7
  | ⟨8, _⟩ => L2_6_8
  | ⟨9, _⟩ => L2_6_9
  | ⟨10, _⟩ => L2_6_10
  | ⟨11, _⟩ => L2_6_11
  | ⟨12, _⟩ => L2_6_12
  | ⟨13, _⟩ => L2_6_13
  | ⟨14, _⟩ => L2_6_14
  | ⟨15, _⟩ => L2_6_15
  | ⟨16, _⟩ => L2_6_16
  | ⟨17, _⟩ => L2_6_17
  | ⟨18, _⟩ => L2_6_18
  | ⟨19, _⟩ => L2_6_19
  | ⟨20, _⟩ => L2_6_20
  | ⟨21, _⟩ => L2_6_21
  | ⟨22, _⟩ => L2_6_22
  | ⟨23, _⟩ => L2_6_23
  | ⟨24, _⟩ => L2_6_24
  | ⟨25, _⟩ => L2_6_25
  | ⟨26, _⟩ => L2_6_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_7_0 : ∀ c : Fin 27, Fast.CertV ![7, 0, c] 2 := by decide +kernel

theorem L2_7_1 : ∀ c : Fin 27, Fast.CertV ![7, 1, c] 2 := by decide +kernel

theorem L2_7_2 : ∀ c : Fin 27, Fast.CertV ![7, 2, c] 2 := by decide +kernel

theorem L2_7_3 : ∀ c : Fin 27, Fast.CertV ![7, 3, c] 2 := by decide +kernel

theorem L2_7_4 : ∀ c : Fin 27, Fast.CertV ![7, 4, c] 2 := by decide +kernel

theorem L2_7_5 : ∀ c : Fin 27, Fast.CertV ![7, 5, c] 2 := by decide +kernel

theorem L2_7_6 : ∀ c : Fin 27, Fast.CertV ![7, 6, c] 2 := by decide +kernel

theorem L2_7_7 : ∀ c : Fin 27, Fast.CertV ![7, 7, c] 2 := by decide +kernel

theorem L2_7_8 : ∀ c : Fin 27, Fast.CertV ![7, 8, c] 2 := by decide +kernel

theorem L2_7_9 : ∀ c : Fin 27, Fast.CertV ![7, 9, c] 2 := by decide +kernel

theorem L2_7_10 : ∀ c : Fin 27, Fast.CertV ![7, 10, c] 2 := by decide +kernel

theorem L2_7_11 : ∀ c : Fin 27, Fast.CertV ![7, 11, c] 2 := by decide +kernel

theorem L2_7_12 : ∀ c : Fin 27, Fast.CertV ![7, 12, c] 2 := by decide +kernel

theorem L2_7_13 : ∀ c : Fin 27, Fast.CertV ![7, 13, c] 2 := by decide +kernel

theorem L2_7_14 : ∀ c : Fin 27, Fast.CertV ![7, 14, c] 2 := by decide +kernel

theorem L2_7_15 : ∀ c : Fin 27, Fast.CertV ![7, 15, c] 2 := by decide +kernel

theorem L2_7_16 : ∀ c : Fin 27, Fast.CertV ![7, 16, c] 2 := by decide +kernel

theorem L2_7_17 : ∀ c : Fin 27, Fast.CertV ![7, 17, c] 2 := by decide +kernel

theorem L2_7_18 : ∀ c : Fin 27, Fast.CertV ![7, 18, c] 2 := by decide +kernel

theorem L2_7_19 : ∀ c : Fin 27, Fast.CertV ![7, 19, c] 2 := by decide +kernel

theorem L2_7_20 : ∀ c : Fin 27, Fast.CertV ![7, 20, c] 2 := by decide +kernel

theorem L2_7_21 : ∀ c : Fin 27, Fast.CertV ![7, 21, c] 2 := by decide +kernel

theorem L2_7_22 : ∀ c : Fin 27, Fast.CertV ![7, 22, c] 2 := by decide +kernel

theorem L2_7_23 : ∀ c : Fin 27, Fast.CertV ![7, 23, c] 2 := by decide +kernel

theorem L2_7_24 : ∀ c : Fin 27, Fast.CertV ![7, 24, c] 2 := by decide +kernel

theorem L2_7_25 : ∀ c : Fin 27, Fast.CertV ![7, 25, c] 2 := by decide +kernel

theorem L2_7_26 : ∀ c : Fin 27, Fast.CertV ![7, 26, c] 2 := by decide +kernel

theorem A2_7 : ∀ b c : Fin 27, Fast.CertV ![7, b, c] 2
  | ⟨0, _⟩ => L2_7_0
  | ⟨1, _⟩ => L2_7_1
  | ⟨2, _⟩ => L2_7_2
  | ⟨3, _⟩ => L2_7_3
  | ⟨4, _⟩ => L2_7_4
  | ⟨5, _⟩ => L2_7_5
  | ⟨6, _⟩ => L2_7_6
  | ⟨7, _⟩ => L2_7_7
  | ⟨8, _⟩ => L2_7_8
  | ⟨9, _⟩ => L2_7_9
  | ⟨10, _⟩ => L2_7_10
  | ⟨11, _⟩ => L2_7_11
  | ⟨12, _⟩ => L2_7_12
  | ⟨13, _⟩ => L2_7_13
  | ⟨14, _⟩ => L2_7_14
  | ⟨15, _⟩ => L2_7_15
  | ⟨16, _⟩ => L2_7_16
  | ⟨17, _⟩ => L2_7_17
  | ⟨18, _⟩ => L2_7_18
  | ⟨19, _⟩ => L2_7_19
  | ⟨20, _⟩ => L2_7_20
  | ⟨21, _⟩ => L2_7_21
  | ⟨22, _⟩ => L2_7_22
  | ⟨23, _⟩ => L2_7_23
  | ⟨24, _⟩ => L2_7_24
  | ⟨25, _⟩ => L2_7_25
  | ⟨26, _⟩ => L2_7_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem L2_8_0 : ∀ c : Fin 27, Fast.CertV ![8, 0, c] 2 := by decide +kernel

theorem L2_8_1 : ∀ c : Fin 27, Fast.CertV ![8, 1, c] 2 := by decide +kernel

theorem L2_8_2 : ∀ c : Fin 27, Fast.CertV ![8, 2, c] 2 := by decide +kernel

theorem L2_8_3 : ∀ c : Fin 27, Fast.CertV ![8, 3, c] 2 := by decide +kernel

theorem L2_8_4 : ∀ c : Fin 27, Fast.CertV ![8, 4, c] 2 := by decide +kernel

theorem L2_8_5 : ∀ c : Fin 27, Fast.CertV ![8, 5, c] 2 := by decide +kernel

theorem L2_8_6 : ∀ c : Fin 27, Fast.CertV ![8, 6, c] 2 := by decide +kernel

theorem L2_8_7 : ∀ c : Fin 27, Fast.CertV ![8, 7, c] 2 := by decide +kernel

theorem L2_8_8 : ∀ c : Fin 27, Fast.CertV ![8, 8, c] 2 := by decide +kernel

theorem L2_8_9 : ∀ c : Fin 27, Fast.CertV ![8, 9, c] 2 := by decide +kernel

theorem L2_8_10 : ∀ c : Fin 27, Fast.CertV ![8, 10, c] 2 := by decide +kernel

theorem L2_8_11 : ∀ c : Fin 27, Fast.CertV ![8, 11, c] 2 := by decide +kernel

theorem L2_8_12 : ∀ c : Fin 27, Fast.CertV ![8, 12, c] 2 := by decide +kernel

theorem L2_8_13 : ∀ c : Fin 27, Fast.CertV ![8, 13, c] 2 := by decide +kernel

theorem L2_8_14 : ∀ c : Fin 27, Fast.CertV ![8, 14, c] 2 := by decide +kernel

theorem L2_8_15 : ∀ c : Fin 27, Fast.CertV ![8, 15, c] 2 := by decide +kernel

theorem L2_8_16 : ∀ c : Fin 27, Fast.CertV ![8, 16, c] 2 := by decide +kernel

theorem L2_8_17 : ∀ c : Fin 27, Fast.CertV ![8, 17, c] 2 := by decide +kernel

theorem L2_8_18 : ∀ c : Fin 27, Fast.CertV ![8, 18, c] 2 := by decide +kernel

theorem L2_8_19 : ∀ c : Fin 27, Fast.CertV ![8, 19, c] 2 := by decide +kernel

theorem L2_8_20 : ∀ c : Fin 27, Fast.CertV ![8, 20, c] 2 := by decide +kernel

theorem L2_8_21 : ∀ c : Fin 27, Fast.CertV ![8, 21, c] 2 := by decide +kernel

theorem L2_8_22 : ∀ c : Fin 27, Fast.CertV ![8, 22, c] 2 := by decide +kernel

theorem L2_8_23 : ∀ c : Fin 27, Fast.CertV ![8, 23, c] 2 := by decide +kernel

theorem L2_8_24 : ∀ c : Fin 27, Fast.CertV ![8, 24, c] 2 := by decide +kernel

theorem L2_8_25 : ∀ c : Fin 27, Fast.CertV ![8, 25, c] 2 := by decide +kernel

theorem L2_8_26 : ∀ c : Fin 27, Fast.CertV ![8, 26, c] 2 := by decide +kernel

theorem A2_8 : ∀ b c : Fin 27, Fast.CertV ![8, b, c] 2
  | ⟨0, _⟩ => L2_8_0
  | ⟨1, _⟩ => L2_8_1
  | ⟨2, _⟩ => L2_8_2
  | ⟨3, _⟩ => L2_8_3
  | ⟨4, _⟩ => L2_8_4
  | ⟨5, _⟩ => L2_8_5
  | ⟨6, _⟩ => L2_8_6
  | ⟨7, _⟩ => L2_8_7
  | ⟨8, _⟩ => L2_8_8
  | ⟨9, _⟩ => L2_8_9
  | ⟨10, _⟩ => L2_8_10
  | ⟨11, _⟩ => L2_8_11
  | ⟨12, _⟩ => L2_8_12
  | ⟨13, _⟩ => L2_8_13
  | ⟨14, _⟩ => L2_8_14
  | ⟨15, _⟩ => L2_8_15
  | ⟨16, _⟩ => L2_8_16
  | ⟨17, _⟩ => L2_8_17
  | ⟨18, _⟩ => L2_8_18
  | ⟨19, _⟩ => L2_8_19
  | ⟨20, _⟩ => L2_8_20
  | ⟨21, _⟩ => L2_8_21
  | ⟨22, _⟩ => L2_8_22
  | ⟨23, _⟩ => L2_8_23
  | ⟨24, _⟩ => L2_8_24
  | ⟨25, _⟩ => L2_8_25
  | ⟨26, _⟩ => L2_8_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

end E1Cert.Table
