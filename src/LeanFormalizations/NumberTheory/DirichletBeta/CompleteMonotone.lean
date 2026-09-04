/-
# Strictly completely monotone sequences — the discrete engine behind N3

`rForm_neg` (the crux, `Integral.lean`) is usually proved by an `s`-fold Beta integral.  This
file replaces the integral by pure sequence algebra:

* `fd f u = f u - f (u+1)` is the forward difference; `StrictCM f` says every iterate
  `fd^[k] f` is strictly positive — the discrete shadow of "`f` is the moment sequence of a
  positive measure on `[0,1]`" (Hausdorff).
* `StrictCM` is closed under shift, difference, sums, positive scalars and **products**
  (the discrete Leibniz rule `fd (f g) = f · fd g + (shift g) · fd f`).  Products are what the
  `s`-fold integral would have provided.
* `alt f u = Σ_v (-1)^v f (u+v)` (the resolvent `(1+E)^{-1}`) preserves `StrictCM` and is
  bounded by `f u - f (u+1) ≤ alt f u ≤ f u`; and a sequence `N` with
  `N u + N (u+1) = P u`, `N → 0`, is exactly `alt P` (`alt_of_recurrence`).
-/
import Mathlib

namespace LeanFormalizations.DirichletBeta

open Finset Filter Topology

/-- Forward difference `Δf(u) = f u - f (u+1)`. -/
def fd (f : ℕ → ℝ) : ℕ → ℝ := fun u => f u - f (u + 1)

/-- Shift `(Ef)(u) = f (u+1)`. -/
def sh (f : ℕ → ℝ) : ℕ → ℝ := fun u => f (u + 1)

/-- Strictly completely monotone: every iterated forward difference is strictly positive. -/
def StrictCM (f : ℕ → ℝ) : Prop := ∀ k u, 0 < fd^[k] f u

lemma fd_apply (f : ℕ → ℝ) (u : ℕ) : fd f u = f u - f (u + 1) := rfl
lemma sh_apply (f : ℕ → ℝ) (u : ℕ) : sh f u = f (u + 1) := rfl

lemma fd_sh (f : ℕ → ℝ) : fd (sh f) = sh (fd f) := rfl

lemma fd_iter_sh (f : ℕ → ℝ) (k : ℕ) : fd^[k] (sh f) = sh (fd^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, fd_sh, ih]

lemma fd_add (f g : ℕ → ℝ) : fd (f + g) = fd f + fd g := by
  funext u; simp only [fd, Pi.add_apply]; ring

lemma fd_iter_add (f g : ℕ → ℝ) (k : ℕ) : fd^[k] (f + g) = fd^[k] f + fd^[k] g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, fd_add, ih]

lemma fd_smul (c : ℝ) (f : ℕ → ℝ) : fd (c • f) = c • fd f := by
  funext u; simp only [fd, Pi.smul_apply, smul_eq_mul]; ring

lemma fd_iter_smul (c : ℝ) (f : ℕ → ℝ) (k : ℕ) : fd^[k] (c • f) = c • fd^[k] f := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, fd_smul, ih]

/-- The discrete Leibniz rule. -/
lemma fd_mul (f g : ℕ → ℝ) : fd (f * g) = f * fd g + sh g * fd f := by
  funext u; simp only [fd, sh, Pi.add_apply, Pi.mul_apply]; ring

lemma fd_iter_pos_apply {f : ℕ → ℝ} (h : StrictCM f) (k u : ℕ) : 0 < fd^[k] f u := h k u

lemma StrictCM.pos {f : ℕ → ℝ} (h : StrictCM f) (u : ℕ) : 0 < f u := h 0 u

lemma StrictCM.diff {f : ℕ → ℝ} (h : StrictCM f) : StrictCM (fd f) := fun k u => by
  rw [← Function.iterate_succ_apply]; exact h (k + 1) u

lemma StrictCM.shift {f : ℕ → ℝ} (h : StrictCM f) : StrictCM (sh f) := fun k u => by
  rw [fd_iter_sh]; exact h k (u + 1)

lemma StrictCM.add {f g : ℕ → ℝ} (hf : StrictCM f) (hg : StrictCM g) : StrictCM (f + g) :=
  fun k u => by rw [fd_iter_add]; exact add_pos (hf k u) (hg k u)

lemma StrictCM.smul {f : ℕ → ℝ} (hf : StrictCM f) {c : ℝ} (hc : 0 < c) : StrictCM (c • f) :=
  fun k u => by rw [fd_iter_smul]; exact mul_pos hc (hf k u)

/-- Products of strictly completely monotone sequences are strictly completely monotone. -/
lemma StrictCM.mul {f g : ℕ → ℝ} (hf : StrictCM f) (hg : StrictCM g) : StrictCM (f * g) := by
  suffices H : ∀ k, ∀ f g : ℕ → ℝ, StrictCM f → StrictCM g → ∀ u, 0 < fd^[k] (f * g) u from
    fun k u => H k f g hf hg u
  intro k
  induction k with
  | zero => intro f g hf hg u; exact mul_pos (hf.pos u) (hg.pos u)
  | succ k ih =>
    intro f g hf hg u
    rw [Function.iterate_succ_apply, fd_mul, fd_iter_add]
    exact add_pos (ih _ _ hf hg.diff u) (ih _ _ hg.shift hf.diff u)

lemma StrictCM.pow {f : ℕ → ℝ} (hf : StrictCM f) {s : ℕ} (hs : 1 ≤ s) : StrictCM (f ^ s) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  induction t with
  | zero => simpa using hf
  | succ t ih => rw [pow_succ]; exact (ih (by omega)).mul hf

lemma StrictCM.antitone {f : ℕ → ℝ} (hf : StrictCM f) : Antitone f :=
  antitone_nat_of_succ_le fun u => by
    have := hf 1 u
    simp only [Function.iterate_one, fd_apply] at this
    linarith

/-! ### Summability bookkeeping -/

lemma summable_sh {f : ℕ → ℝ} (hf : Summable f) : Summable (sh f) :=
  (summable_nat_add_iff 1).2 hf

lemma summable_fd {f : ℕ → ℝ} (hf : Summable f) : Summable (fd f) :=
  hf.sub (summable_sh hf)

lemma summable_fd_iter {f : ℕ → ℝ} (hf : Summable f) (k : ℕ) : Summable (fd^[k] f) := by
  induction k generalizing f with
  | zero => simpa using hf
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (summable_fd hf)

/-! ### The alternating resolvent `alt` -/

/-- `alt f u = Σ_{v ≥ 0} (-1)^v f (u + v)`. -/
noncomputable def alt (f : ℕ → ℝ) : ℕ → ℝ := fun u => ∑' v, (-1 : ℝ) ^ v * f (u + v)

lemma summable_alt_term {f : ℕ → ℝ} (hf : Summable f) (u : ℕ) :
    Summable (fun v => (-1 : ℝ) ^ v * f (u + v)) := by
  have h : Summable (fun v => f (u + v)) := by
    have := (summable_nat_add_iff u).2 hf
    refine this.congr fun v => ?_
    simp [add_comm]
  refine Summable.of_norm_bounded h.abs fun v => ?_
  simp

lemma alt_hasSum {f : ℕ → ℝ} (hf : Summable f) (u : ℕ) :
    HasSum (fun v => (-1 : ℝ) ^ v * f (u + v)) (alt f u) :=
  (summable_alt_term hf u).hasSum

lemma fd_alt {f : ℕ → ℝ} (hf : Summable f) : fd (alt f) = alt (fd f) := by
  funext u
  simp only [fd_apply, alt]
  rw [← (summable_alt_term hf u).tsum_sub (summable_alt_term hf (u + 1))]
  refine tsum_congr fun v => ?_
  rw [show u + 1 + v = u + v + 1 by ring]
  ring

lemma fd_iter_alt {f : ℕ → ℝ} (hf : Summable f) (k : ℕ) :
    fd^[k] (alt f) = alt (fd^[k] f) := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, fd_alt hf,
      ih (summable_fd hf)]

/-- The alternating series of an antitone summable sequence is at least its first difference. -/
lemma sub_le_alt {f : ℕ → ℝ} (hf : Summable f) (ha : Antitone f) (u : ℕ) :
    f u - f (u + 1) ≤ alt f u := by
  have hl := (alt_hasSum hf u).tendsto_sum_nat
  have ha' : Antitone (fun v => f (u + v)) := fun a b hab => ha (by omega)
  have := Antitone.alternating_series_le_tendsto hl ha' 1
  simpa [Finset.sum_range_succ] using this

/-- The alternating series of an antitone summable sequence is at most its first term. -/
lemma alt_le {f : ℕ → ℝ} (hf : Summable f) (ha : Antitone f) (u : ℕ) : alt f u ≤ f u := by
  have hl := (alt_hasSum hf u).tendsto_sum_nat
  have ha' : Antitone (fun v => f (u + v)) := fun a b hab => ha (by omega)
  have := Antitone.tendsto_le_alternating_series hl ha' 0
  simpa using this

/-- Iterated differences of a `StrictCM` sequence are `StrictCM`. -/
lemma StrictCM.diff_iter {f : ℕ → ℝ} (hf : StrictCM f) (k : ℕ) : StrictCM (fd^[k] f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.diff

/-- `alt` preserves strict complete monotonicity. -/
lemma StrictCM.alt {f : ℕ → ℝ} (hf : StrictCM f) (hs : Summable f) : StrictCM (alt f) := by
  intro k u
  rw [fd_iter_alt hs]
  have h1 := sub_le_alt (summable_fd_iter hs k) (hf.diff_iter k).antitone u
  have h2 := hf (k + 1) u
  rw [Function.iterate_succ_apply', fd_apply] at h2
  linarith

/-- **Telescoping.**  If `N u + N (u+1) = P u` for all `u`, `N → 0`, and `P` is summable, then
`N = alt P`. -/
lemma alt_of_recurrence {N P : ℕ → ℝ} (hrec : ∀ u, N u + N (u + 1) = P u)
    (hN : Tendsto N atTop (𝓝 0)) (hP : Summable P) : N = alt P := by
  funext u
  have hpartial : ∀ V, ∑ v ∈ range V, (-1 : ℝ) ^ v * P (u + v) = N u - (-1) ^ V * N (u + V) := by
    intro V
    induction V with
    | zero => simp
    | succ V ih =>
      rw [Finset.sum_range_succ, ih, ← hrec (u + V), pow_succ]
      rw [show u + (V + 1) = u + V + 1 by ring]
      ring
  have hlim : Tendsto (fun V => ∑ v ∈ range V, (-1 : ℝ) ^ v * P (u + v)) atTop (𝓝 (N u)) := by
    simp_rw [hpartial]
    have h0 : Tendsto (fun V => (-1 : ℝ) ^ V * N (u + V)) atTop (𝓝 0) := by
      have hN' : Tendsto (fun V => N (u + V)) atTop (𝓝 0) := by
        have := hN.comp (tendsto_add_atTop_nat u)
        refine this.congr fun V => ?_
        simp [Function.comp, add_comm]
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_zero_iff_norm_tendsto_zero.1 hN').congr fun V => ?_
      simp
    simpa using (tendsto_const_nhds (x := N u)).sub h0
  exact tendsto_nhds_unique hlim (alt_hasSum hP u).tendsto_sum_nat

end LeanFormalizations.DirichletBeta
