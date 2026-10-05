/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import LeanFormalizations.NumberTheory.Mills.E1CertTable10
import LeanFormalizations.NumberTheory.Mills.E1CertTable11
import LeanFormalizations.NumberTheory.Mills.E1CertTable12
import LeanFormalizations.NumberTheory.Mills.E1CertTable20
import LeanFormalizations.NumberTheory.Mills.E1CertTable21
import LeanFormalizations.NumberTheory.Mills.E1CertTable22

/-!
# Phase 61, E1: `cert_all`

The certificate holds in all `2 · 27³` cases, by `decide +kernel` on the fast form
`Fast.CertV` (tables `E1CertTable*`), transferred by `cert_of_certV`.
-/

namespace E1Cert

namespace Table

theorem T1 : ∀ a b c : Fin 27, Fast.CertV ![a, b, c] 1
  | ⟨0, _⟩ => A1_0
  | ⟨1, _⟩ => A1_1
  | ⟨2, _⟩ => A1_2
  | ⟨3, _⟩ => A1_3
  | ⟨4, _⟩ => A1_4
  | ⟨5, _⟩ => A1_5
  | ⟨6, _⟩ => A1_6
  | ⟨7, _⟩ => A1_7
  | ⟨8, _⟩ => A1_8
  | ⟨9, _⟩ => A1_9
  | ⟨10, _⟩ => A1_10
  | ⟨11, _⟩ => A1_11
  | ⟨12, _⟩ => A1_12
  | ⟨13, _⟩ => A1_13
  | ⟨14, _⟩ => A1_14
  | ⟨15, _⟩ => A1_15
  | ⟨16, _⟩ => A1_16
  | ⟨17, _⟩ => A1_17
  | ⟨18, _⟩ => A1_18
  | ⟨19, _⟩ => A1_19
  | ⟨20, _⟩ => A1_20
  | ⟨21, _⟩ => A1_21
  | ⟨22, _⟩ => A1_22
  | ⟨23, _⟩ => A1_23
  | ⟨24, _⟩ => A1_24
  | ⟨25, _⟩ => A1_25
  | ⟨26, _⟩ => A1_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

theorem T2 : ∀ a b c : Fin 27, Fast.CertV ![a, b, c] 2
  | ⟨0, _⟩ => A2_0
  | ⟨1, _⟩ => A2_1
  | ⟨2, _⟩ => A2_2
  | ⟨3, _⟩ => A2_3
  | ⟨4, _⟩ => A2_4
  | ⟨5, _⟩ => A2_5
  | ⟨6, _⟩ => A2_6
  | ⟨7, _⟩ => A2_7
  | ⟨8, _⟩ => A2_8
  | ⟨9, _⟩ => A2_9
  | ⟨10, _⟩ => A2_10
  | ⟨11, _⟩ => A2_11
  | ⟨12, _⟩ => A2_12
  | ⟨13, _⟩ => A2_13
  | ⟨14, _⟩ => A2_14
  | ⟨15, _⟩ => A2_15
  | ⟨16, _⟩ => A2_16
  | ⟨17, _⟩ => A2_17
  | ⟨18, _⟩ => A2_18
  | ⟨19, _⟩ => A2_19
  | ⟨20, _⟩ => A2_20
  | ⟨21, _⟩ => A2_21
  | ⟨22, _⟩ => A2_22
  | ⟨23, _⟩ => A2_23
  | ⟨24, _⟩ => A2_24
  | ⟨25, _⟩ => A2_25
  | ⟨26, _⟩ => A2_26
  | ⟨n + 27, h⟩ => absurd h (by omega)

end Table

theorem cert_all : ∀ t : Fin 3, t = 1 ∨ t = 2 → ∀ a b c : Fin 27, Cert ![a, b, c] t := by
  intro t ht a b c
  rcases ht with rfl | rfl
  · exact cert_of_certV (Table.T1 a b c)
  · exact cert_of_certV (Table.T2 a b c)

end E1Cert
