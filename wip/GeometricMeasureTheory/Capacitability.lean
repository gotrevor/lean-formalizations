/-
# Capacitability: "analytic sets are universally (`NullMeasurable`) measurable"

This is the sole remaining hole of the `jvn` / von Neumann measurable-selection route
(`VonNeumannSelection.lean`): brick A,

  `analyticSet_nullMeasurableSet : AnalyticSet s → NullMeasurableSet s μ`

i.e. **Choquet's capacitability theorem** (analytic sets are universally measurable). mathlib has the
`AnalyticSet` API + Lusin separation (`AnalyticSet.measurableSet_of_compl`) but **no** capacity /
Souslin-operation machinery, so this is a from-scratch DST build.

`lake env lean wip/GeometricMeasureTheory/Capacitability.lean` kernel-checks it.

## What is PROVEN here (no `sorry`) — the whole reduction is now machine-checked
The headline `analyticSet_nullMeasurableSet` (σ-finite `μ`) is reduced, with NO remaining hole except
the single finite-measure Choquet core, by two proven steps:

* `analyticSet_nullMeasurableSet_finite` (PROVEN from the core): for a **finite** measure, inner
  approximation by compacts ⟹ `NullMeasurable`. Sandwich `F = ⋃ Kₙ ⊆ s ⊆ G = toMeasurable μ s` with
  `μ F = μ s = μ G`, so `μ (s \ F) ≤ μ (G \ F) = 0` and `s =ᵐ[μ] F` (`ae_eq_set`).
* `analyticSet_nullMeasurableSet` (PROVEN from the finite case): **σ-finite reduction** via
  `spanningSets`. `s = ⋃ₙ (s ∩ spanningSets μ n)`; on each finite piece `μ.restrict (spanningSets μ n)`
  is finite, the finite case applies, and `nullMeasurableSet_restrict` transfers
  `NullMeasurableSet s (μ.restrict Dₙ)` to `NullMeasurableSet (s ∩ Dₙ) μ`; union closes it.

## The SOLE remaining hole: the finite Choquet core
`exists_isCompact_subset_outerMeasure_le` (finite `μ`): for analytic `s` and `ε > 0`, a compact
`K ⊆ s` with `μ s ≤ μ K + ε`. This is the genuine content of Choquet's theorem (inner regularity of
analytic sets by compacts). The Souslin scheme of cylinder images is set up below
(`cylImg`/`_zero`/`_decomp`/`analyticSet_cylImg`); the argument (Kechris 29.7 / Cohn, App.) is:

Let `f : (ℕ→ℕ) → X` continuous with `range f = s` (a nonempty analytic set;
`VonNeumann.analyticSet_exists_nat_nat_range`). The **Souslin scheme** is `A σ n := f '' cylinder σ n`.
For finite `μ` with outer measure `μ*`:
* `μ*` is monotone and continuous from below; at each scheme node a finite sub-union of children captures
  all but `ε·2⁻ⁿ` of the measure (the **regularisation**);
* the pruned finitely-branching subtree `C = {α | ∀ i, α i ≤ nᵢ}` is **compact** in `ℕ→ℕ` (a closed
  subset of `∏ᵢ Finset.range (nᵢ+1)`), so `K = f '' C` is compact, `K ⊆ s`, and the regularisation
  budget gives `μ* s ≤ μ K + ε` (the **measure-extraction core**);
* (already discharged here) inner + outer regularity ⇒ `NullMeasurable`.
A port of `RemyDegenne/brownian-motion`'s `Choquet/` stack (see the online-research request) is the mechanical
alternative to this from-scratch proof; whichever lands first discharges the core.
-/
import Mathlib

open MeasureTheory Set Topology Function Filter
open scoped ENNReal

open PiNat

/-! ## Aristotle-generated, kernel-verified Choquet capacitability core (ported 2026-06-19).
Self-contained Lusin-scheme proof of `choquet_core_range`; `#print axioms` clean. -/
namespace ChoquetAux

/-! ## Cylinders of Baire space indexed by finite codes -/

/-- `res` depends only on the first `n` coordinates. -/
theorem res_congr (x y : ℕ → ℕ) (n : ℕ) (h : ∀ i < n, x i = y i) : res x n = res y n := by
  induction n with
  | zero => simp [res]
  | succ k ih => rw [res_succ, res_succ, h k (by omega), ih (fun i hi => h i (by omega))]

/-- Every finite list is realized as a `res`. -/
theorem exists_res (l : List ℕ) : ∃ x : ℕ → ℕ, res x l.length = l := by
  induction l with
  | nil => exact ⟨fun _ => 0, rfl⟩
  | cons a t ih =>
    obtain ⟨x, hx⟩ := ih
    refine ⟨Function.update x t.length a, ?_⟩
    show res (Function.update x t.length a) (t.length + 1) = a :: t
    rw [res_succ, Function.update_self]
    congr 1
    rw [res_congr (Function.update x t.length a) x t.length
      (fun i hi => Function.update_of_ne (Nat.ne_of_lt hi) a x)]
    exact hx

/-- The cylinder of `ℕ → ℕ` determined by the finite code `l : List ℕ`. -/
def Cyl (l : List ℕ) : Set (ℕ → ℕ) := {α | PiNat.res α l.length = l}

@[simp] theorem mem_Cyl {l : List ℕ} {α : ℕ → ℕ} : α ∈ Cyl l ↔ PiNat.res α l.length = l :=
  Iff.rfl

theorem Cyl_nil : Cyl ([] : List ℕ) = Set.univ := by ext α; simp [Cyl]

/-- A concrete sequence realizing the code `l`. -/
noncomputable def extend (l : List ℕ) : ℕ → ℕ := Classical.choose (exists_res l)

theorem res_extend (l : List ℕ) : res (extend l) l.length = l := Classical.choose_spec (exists_res l)

theorem Cyl_nonempty (l : List ℕ) : (Cyl l).Nonempty := ⟨extend l, res_extend l⟩

theorem Cyl_eq_cylinder (l : List ℕ) : Cyl l = PiNat.cylinder (extend l) l.length := by
  rw [PiNat.cylinder_eq_res, res_extend]; rfl

theorem isClosed_cylinder (x : ℕ → ℕ) (n : ℕ) : IsClosed (PiNat.cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]; exact isClosed_set_pi (fun i _ => isClosed_singleton)

theorem isOpen_Cyl (l : List ℕ) : IsOpen (Cyl l) := by
  rw [Cyl_eq_cylinder]; exact PiNat.isOpen_cylinder _ _ _

theorem isClosed_Cyl (l : List ℕ) : IsClosed (Cyl l) := by
  rw [Cyl_eq_cylinder]; exact isClosed_cylinder _ _

/-- A child cylinder is contained in its parent. -/
theorem Cyl_cons_subset (a : ℕ) (l : List ℕ) : Cyl (a :: l) ⊆ Cyl l := by
  intro α hα
  simp only [Cyl, mem_setOf_eq] at hα ⊢
  have h : (a :: l).length = l.length + 1 := rfl
  rw [h, res_succ] at hα
  exact (List.cons.injEq _ _ _ _ ▸ hα).2

/-- A cylinder is the union of its immediate children. -/
theorem Cyl_eq_iUnion_cons (l : List ℕ) : Cyl l = ⋃ a, Cyl (a :: l) := by
  ext α
  simp only [Cyl, mem_setOf_eq, mem_iUnion]
  constructor
  · intro h
    refine ⟨α l.length, ?_⟩
    show res α (l.length + 1) = α l.length :: l
    rw [res_succ, h]
  · rintro ⟨a, ha⟩
    show res α l.length = l
    have h : (a :: l).length = l.length + 1 := rfl
    rw [h, res_succ] at ha
    exact (List.cons.injEq _ _ _ _ ▸ ha).2

/-- Equality of `res` at length `n` is equivalent to agreement on the first `n` coordinates. -/
theorem res_eq_iff (x y : ℕ → ℕ) (n : ℕ) : res x n = res y n ↔ ∀ i < n, x i = y i := by
  constructor
  · intro h i hi
    have hy : y ∈ PiNat.cylinder x n := by rw [PiNat.cylinder_eq_res]; exact h.symm
    exact (PiNat.mem_cylinder_iff.1 hy i hi).symm
  · exact fun h => res_congr x y n h

/-- Longer `res`-cylinders are contained in shorter ones. -/
theorem Cyl_res_anti (α : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) : Cyl (res α m) ⊆ Cyl (res α n) := by
  intro β hβ
  simp only [mem_Cyl, res_length] at hβ ⊢
  rw [res_eq_iff] at hβ ⊢
  exact fun i hi => hβ i (lt_of_lt_of_le hi h)

/-
A nested sequence of cylinders whose lengths tend to infinity has a common point.
-/
theorem iInter_Cyl_nonempty (g : ℕ → List ℕ)
    (hmono : ∀ n, Cyl (g (n + 1)) ⊆ Cyl (g n))
    (hlen : Filter.Tendsto (fun n => (g n).length) Filter.atTop Filter.atTop) :
    (⋂ n, Cyl (g n)).Nonempty := by
  -- Equip `ℕ → ℕ` with the PiNat metric: `letI := PiNat.metricSpaceNatNat` and obtain `CompleteSpace` from `PiNat.completeSpace`.
  letI : MetricSpace (ℕ → ℕ) := PiNat.metricSpaceNatNat
  have h_complete : CompleteSpace (ℕ → ℕ) := by
    infer_instance;
  -- Define `u n := extend (g n)`, so `u n ∈ Cyl (g n)` by `res_extend`, and `Cyl (g n) = PiNat.cylinder (extend (g n)) (g n).length` via `Cyl_eq_cylinder`.
  set u : ℕ → ℕ → ℕ := fun n => extend (g n);
  -- Show `(u n)` is a Cauchy sequence. Key fact: for `n ≤ m`, since the cylinders are nested (`hmono` iterated, giving `Cyl (g m) ⊆ Cyl (g n)`), we have `u m ∈ Cyl (g m) ⊆ Cyl (g n)`, hence `res (u m) (g n).length = g n = res (u n) (g n).length`, i.e. `u m` and `u n` agree on the first `(g n).length` coordinates.
  have h_cauchy : CauchySeq u := by
    have h_dist : ∀ n m : ℕ, n ≤ m → dist (u m) (u n) ≤ (1 / 2 : ℝ) ^ ((g n).length) := by
      intros n m hnm
      have h_agree : PiNat.res (u m) (g n).length = PiNat.res (u n) (g n).length := by
        have h_agree : ∀ n m : ℕ, n ≤ m → Cyl (g m) ⊆ Cyl (g n) := by
          exact fun n m hnm => by induction hnm <;> [ tauto; exact Set.Subset.trans ( hmono _ ) ‹_› ] ;
        have h_agree : u m ∈ Cyl (g n) := by
          exact h_agree n m hnm ( res_extend _ );
        exact h_agree.trans ( res_extend _ |> Eq.symm );
      convert PiNat.mem_cylinder_iff_dist_le.mp _ using 1;
      convert h_agree using 1;
      simp +decide [ PiNat.cylinder, res_eq_iff ];
    refine' Metric.cauchySeq_iff'.2 _;
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (1 / 2 : ℝ) ^ ((g n).length) < ε := by
      simpa using ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num : ( 1 : ℝ ) / 2 < 1 ) ) |> fun h => h.comp hlen |> fun h => h.eventually ( gt_mem_nhds hε_pos );
    exact ⟨ N, fun n hn => lt_of_le_of_lt ( h_dist _ _ hn ) ( hN _ le_rfl ) ⟩;
  obtain ⟨ α, hα ⟩ := cauchySeq_tendsto_of_complete h_cauchy;
  refine' ⟨ α, Set.mem_iInter.2 fun n => _ ⟩;
  -- Since `Cyl (g n)` is closed and `u m ∈ Cyl (g n)` for all `m ≥ n`, the limit `α ∈ Cyl (g n)` by `IsClosed.mem_of_tendsto`.
  have h_closed : IsClosed (Cyl (g n)) := by
    exact?;
  exact h_closed.mem_of_tendsto hα ( Filter.eventually_atTop.mpr ⟨ n, fun m hm => by exact Set.mem_of_subset_of_mem ( show Cyl ( g m ) ⊆ Cyl ( g n ) from by exact Nat.le_induction ( by tauto ) ( fun k hk ih => by tauto ) m hm ) ( show u m ∈ Cyl ( g m ) from by exact res_extend _ ) ⟩ )

/-! ## The refinement step and the Lusin scheme -/

variable {X : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]
variable (f : (ℕ → ℕ) → X) (hf : Continuous f)

include hf

/-
**Refinement step.** Any cylinder `Cyl w` can be covered by countably many sub-cylinders
each of whose `f`-image has diameter `≤ r`, and which are strictly longer than `w`.
-/
theorem refineStep (w : List ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ e : ℕ → List ℕ,
      (∀ a, w.length < (e a).length) ∧
      (∀ a, Metric.ediam (f '' Cyl (e a)) ≤ ENNReal.ofReal r) ∧
      Cyl w = ⋃ a, Cyl (e a) := by
  revert w;
  intro w
  set S := {v : List ℕ | w.length < v.length ∧ Cyl v ⊆ Cyl w ∧ Metric.ediam (f '' Cyl v) ≤ ENNReal.ofReal r} with hS_def
  have hS_countable : S.Countable := by
    exact Set.to_countable S
  have hS_univ : Cyl w ⊆ ⋃ v ∈ S, Cyl v := by
    intro α hα
    obtain ⟨k, hk⟩ : ∃ k, w.length < k ∧ Metric.ediam (f '' Cyl (res α k)) ≤ ENNReal.ofReal r := by
      -- By continuity of $f$, there exists a neighborhood $U$ of $\alpha$ such that $f(U)$ has diameter $\leq r/2$.
      obtain ⟨U, hU⟩ : ∃ U : Set (ℕ → ℕ), IsOpen U ∧ α ∈ U ∧ Metric.ediam (f '' U) ≤ ENNReal.ofReal (r / 2) := by
        have h_cont : ∀ ε > 0, ∃ U : Set (ℕ → ℕ), IsOpen U ∧ α ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) < ε := by
          intro ε εpos
          obtain ⟨U, hU⟩ : ∃ U : Set (ℕ → ℕ), IsOpen U ∧ α ∈ U ∧ ∀ x ∈ U, dist (f x) (f α) < ε / 2 := by
            exact ⟨ { x | dist ( f x ) ( f α ) < ε / 2 }, isOpen_lt ( hf.dist continuous_const ) continuous_const, by simpa using half_pos εpos, fun x hx => hx ⟩;
          exact ⟨ U, hU.1, hU.2.1, fun x hx y hy => lt_of_le_of_lt ( dist_triangle_right _ _ _ ) ( by linarith [ hU.2.2 x hx, hU.2.2 y hy ] ) ⟩;
        obtain ⟨ U, hU₁, hU₂, hU₃ ⟩ := h_cont ( r / 2 ) ( half_pos hr );
        refine' ⟨ U, hU₁, hU₂, _ ⟩;
        rw [ Metric.ediam_le_iff ];
        rintro _ ⟨ x, hx, rfl ⟩ _ ⟨ y, hy, rfl ⟩ ; exact ENNReal.ofReal_le_ofReal ( le_of_lt ( hU₃ x hx y hy ) ) |> le_trans ( by simp +decide [ edist_dist ] ) ;
      -- By the basis property of cylinders, there exists a cylinder $Cyl v$ such that $\alpha \in Cyl v \subseteq U$.
      obtain ⟨v, hv⟩ : ∃ v : List ℕ, α ∈ Cyl v ∧ Cyl v ⊆ U := by
        have := PiNat.isTopologicalBasis_cylinders;
        specialize this ( fun _ => ℕ );
        have := this.mem_nhds_iff.mp ( hU.1.mem_nhds hU.2.1 );
        obtain ⟨ t, ⟨ x, n, rfl ⟩, ht₁, ht₂ ⟩ := this; use res x n; simp_all +decide [ PiNat.cylinder_eq_res ] ;
        exact fun y hy => ht₂ <| by simpa [ Cyl ] using hy;
      -- Choose $k$ such that $k > \max(w.length, v.length)$.
      obtain ⟨k, hk⟩ : ∃ k, w.length < k ∧ v.length < k ∧ Cyl (res α k) ⊆ Cyl v := by
        refine' ⟨ Max.max ( w.length + 1 ) ( v.length + 1 ), _, _, _ ⟩ <;> simp_all +decide [ Cyl_res_anti ];
        grind +suggestions;
      refine' ⟨ k, hk.1, le_trans ( Metric.ediam_mono <| Set.image_mono <| show Cyl ( res α k ) ⊆ U from hk.2.2.trans hv.2 ) ( hU.2.2.trans <| ENNReal.ofReal_le_ofReal <| by linarith ) ⟩;
    simp +zetaDelta at *;
    refine' ⟨ res α k, ⟨ _, _, hk.2 ⟩, _ ⟩;
    · aesop;
    · exact Cyl_res_anti α hk.1.le |> Set.Subset.trans <| by aesop;
    · simp +decide [ res ]
  have hS_nonempty : S.Nonempty := by
    exact Set.nonempty_iff_ne_empty.2 fun h => by simpa [ h ] using hS_univ ( Cyl_nonempty w |> Classical.choose_spec ) ;
  obtain ⟨e, he⟩ : ∃ e : ℕ → S, Function.Surjective e := by
    have := hS_countable.exists_eq_range;
    exact Exists.elim ( this hS_nonempty ) fun f hf => ⟨ fun n => ⟨ f n, hf.symm.subset ( Set.mem_range_self n ) ⟩, fun x => by rcases hf.subset x.2 with ⟨ n, hn ⟩ ; exact ⟨ n, Subtype.ext hn ⟩ ⟩;
  refine' ⟨ fun a => e a |>.1, _, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
  · exact fun a => ( e a ).2.1;
  · exact fun a => ( e a ).2.2.2;
  · intro x; specialize hS_univ; replace hS_univ := @hS_univ x; simp_all +decide [ Set.subset_def ] ;
    exact ⟨ fun hx => by obtain ⟨ i, hi, hi' ⟩ := hS_univ hx; obtain ⟨ j, hj ⟩ := he ⟨ i, hi ⟩ ; use j; aesop, fun hx => by obtain ⟨ i, hi ⟩ := hx; have := e i |>.2.2.1; aesop ⟩

/-- The Lusin scheme code: `phi l` is the actual Baire cylinder code attached to abstract node `l`. -/
noncomputable def phi : List ℕ → List ℕ
  | [] => []
  | (a :: l) =>
      Classical.choose (refineStep f hf (phi l) ((1 / 2) ^ (l.length + 1)) (by positivity)) a

theorem phi_nil : phi f hf [] = [] := rfl

theorem phi_spec (l : List ℕ) :
    (∀ a, (phi f hf l).length < (phi f hf (a :: l)).length) ∧
    (∀ a, Metric.ediam (f '' Cyl (phi f hf (a :: l))) ≤ ENNReal.ofReal ((1 / 2) ^ (l.length + 1))) ∧
    Cyl (phi f hf l) = ⋃ a, Cyl (phi f hf (a :: l)) := by
  have h := Classical.choose_spec
    (refineStep f hf (phi f hf l) ((1 / 2) ^ (l.length + 1)) (by positivity))
  refine ⟨?_, ?_, ?_⟩
  · intro a; exact h.1 a
  · intro a; exact h.2.1 a
  · exact h.2.2

theorem phi_len_lt (a : ℕ) (l : List ℕ) : (phi f hf l).length < (phi f hf (a :: l)).length :=
  (phi_spec f hf l).1 a

theorem phi_diam (a : ℕ) (l : List ℕ) :
    Metric.ediam (f '' Cyl (phi f hf (a :: l))) ≤ ENNReal.ofReal ((1 / 2) ^ (l.length + 1)) :=
  (phi_spec f hf l).2.1 a

theorem phi_cover (l : List ℕ) : Cyl (phi f hf l) = ⋃ a, Cyl (phi f hf (a :: l)) :=
  (phi_spec f hf l).2.2

theorem phi_len_ge (l : List ℕ) : l.length ≤ (phi f hf l).length := by
  induction l with
  | nil => simp [phi_nil]
  | cons a t ih =>
    have := phi_len_lt f hf a t
    simp only [List.length_cons]
    omega

theorem Cyl_phi_cons_subset (a : ℕ) (l : List ℕ) : Cyl (phi f hf (a :: l)) ⊆ Cyl (phi f hf l) := by
  rw [phi_cover f hf l]; exact subset_iUnion (fun a => Cyl (phi f hf (a :: l))) a

/-! ## The scheme of closed sets -/

/-- The closed set attached to node `l`. -/
def Asc (l : List ℕ) : Set X := closure (f '' Cyl (phi f hf l))

theorem Asc_closed (l : List ℕ) : IsClosed (Asc f hf l) := isClosed_closure

theorem Asc_nonempty (l : List ℕ) : (Asc f hf l).Nonempty :=
  ((Cyl_nonempty (phi f hf l)).image f).closure

theorem Asc_antitone (a : ℕ) (l : List ℕ) : Asc f hf (a :: l) ⊆ Asc f hf l :=
  closure_mono (image_mono (Cyl_phi_cons_subset f hf a l))

theorem Asc_diam (a : ℕ) (l : List ℕ) :
    Metric.ediam (Asc f hf (a :: l)) ≤ ENNReal.ofReal ((1 / 2) ^ (l.length + 1)) := by
  rw [Asc, Metric.ediam_closure]; exact phi_diam f hf a l

theorem Asc_eq_iUnion_image (l : List ℕ) :
    f '' Cyl (phi f hf l) = ⋃ a, f '' Cyl (phi f hf (a :: l)) := by
  rw [phi_cover f hf l, image_iUnion]

/-! ## Branch extraction and convergence -/

/-
If `x` lies in `Asc (res β n)` along a branch `β` whose `phi`-codes have lengths tending to
infinity, then `x` is in the range of `f`.
-/
theorem mem_range_of_branch (x : X) (β : ℕ → ℕ)
    (hx : ∀ n, x ∈ Asc f hf (res β n)) : x ∈ range f := by
  -- Set `g n := phi f hf (res β n)`.
  set g : ℕ → List ℕ := fun n => phi f hf (res β n);
  obtain ⟨α, hα⟩ : ∃ α : ℕ → ℕ, ∀ n, α ∈ Cyl (g n) := by
    convert iInter_Cyl_nonempty g _ _;
    · exact ⟨ fun h => Set.mem_iInter.2 fun n => h n, fun h => fun n => Set.mem_iInter.1 h n ⟩;
    · grind +suggestions;
    · refine' Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop;
      exact fun n => mod_cast phi_len_ge f hf _ |> le_trans ( by simp +decide [ res_length ] );
  -- To show `x = f α`, bound `edist x (f α)`. For each `n ≥ 1`: `res β n = β (n-1) :: res β (n-1)`, so by `phi_diam`, `Metric.ediam (f '' Cyl (g n)) ≤ ENNReal.ofReal ((1/2) ^ n)`.
  have h_edist : ∀ n ≥ 1, edist x (f α) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro n hn
    have h_edist : edist x (f α) ≤ Metric.ediam (Asc f hf (res β n)) := by
      apply Metric.edist_le_ediam_of_mem;
      · exact hx n;
      · exact subset_closure ( Set.mem_image_of_mem _ ( hα n ) );
    convert h_edist.trans _;
    convert Asc_diam f hf ( β ( n - 1 ) ) ( res β ( n - 1 ) ) using 1;
    · cases n <;> aesop;
    · rw [ res_length, Nat.sub_add_cancel hn ];
  -- Since `ENNReal.ofReal ((1/2)^n) → 0` as `n → ∞`, we get `edist x (f α) ≤ 0`, so `edist x (f α) = 0`, hence `x = f α`.
  have h_edist_zero : edist x (f α) = 0 := by
    have h_edist_zero : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num : ( 1 : ℝ ) / 2 < 1 ) );
    exact le_antisymm ( le_of_tendsto_of_tendsto tendsto_const_nhds h_edist_zero ( Filter.eventually_atTop.mpr ⟨ 1, h_edist ⟩ ) ) bot_le;
  aesop

/-! ## Measure regularisation -/

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- Truncated analytic union over a finite set of codes. -/
def Pset (S : Finset (List ℕ)) : Set X := ⋃ l ∈ S, f '' Cyl (phi f hf l)

/-- Truncated closed union over a finite set of codes. -/
def Bset (S : Finset (List ℕ)) : Set X := ⋃ l ∈ S, Asc f hf l

theorem Pset_subset_Bset (S : Finset (List ℕ)) : Pset f hf S ⊆ Bset f hf S := by
  apply iUnion₂_mono; intro l _; exact subset_closure

theorem isClosed_Bset (S : Finset (List ℕ)) : IsClosed (Bset f hf S) := by
  apply Set.Finite.isClosed_biUnion S.finite_toSet
  intro l _; exact Asc_closed f hf l

theorem measurableSet_Bset (S : Finset (List ℕ)) : MeasurableSet (Bset f hf S) :=
  (isClosed_Bset f hf S).measurableSet

/-- The next generation of codes: extend each code in `S` by one symbol `≤ m`. -/
def nextSurv (S : Finset (List ℕ)) (m : ℕ) : Finset (List ℕ) :=
  S.biUnion (fun l => (Finset.range (m + 1)).image (fun a => a :: l))

theorem Pset_nextSurv (S : Finset (List ℕ)) (m : ℕ) :
    Pset f hf (nextSurv S m) = ⋃ l ∈ S, ⋃ a ∈ Finset.range (m + 1), f '' Cyl (phi f hf (a :: l)) := by
  simp [Pset, nextSurv]

/-
**Bound choice.** Choosing the truncation level `m` large keeps almost all the measure.
-/
theorem exists_bound (S : Finset (List ℕ)) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ m : ℕ, μ (Pset f hf S) ≤ μ (Pset f hf (nextSurv S m)) + δ := by
  -- By definition of $Pset$, we know that $Pset f hf (nextSurv S m)$ is the union of $f '' Cyl (phi f hf (a :: l))$ over $a \in Finset.range (m + 1)$ and $l \in S$.
  have h_Pset_nextSurv : ∀ m, μ (Pset f hf (nextSurv S m)) = μ (⋃ l ∈ S, ⋃ a ∈ Finset.range (m + 1), f '' Cyl (phi f hf (a :: l))) := by
    intro m
    rw [Pset_nextSurv];
  have hPset_nextSurv : Filter.Tendsto (fun m => μ (⋃ l ∈ S, ⋃ a ∈ Finset.range (m + 1), f '' Cyl (phi f hf (a :: l)))) Filter.atTop (nhds (μ (⋃ l ∈ S, ⋃ a : ℕ, f '' Cyl (phi f hf (a :: l)))) ) := by
    convert MeasureTheory.tendsto_measure_iUnion_atTop _;
    · ext x; simp [Set.mem_iUnion];
      exact ⟨ fun ⟨ l, hl, a, x, hx, hx' ⟩ => ⟨ a, l, hl, a, le_rfl, x, hx, hx' ⟩, fun ⟨ a, l, hl, b, hb, x, hx, hx' ⟩ => ⟨ l, hl, b, x, hx, hx' ⟩ ⟩;
    · infer_instance;
    · exact fun m n hmn => Set.iUnion₂_mono fun l hl => Set.iUnion₂_mono' fun a ha => ⟨ a, Finset.mem_range.mpr ( by linarith [ Finset.mem_range.mp ha ] ), Set.Subset.rfl ⟩;
  have hPset_nextSurv : μ (⋃ l ∈ S, ⋃ a : ℕ, f '' Cyl (phi f hf (a :: l))) = μ (Pset f hf S) := by
    congr;
    grind +suggestions;
  simp_all +decide [ ENNReal.tendsto_nhds ];
  exact Exists.elim ( ‹∀ ε : ℝ≥0∞, 0 < ε → ∃ a, ∀ b : ℕ, a ≤ b → μ ( Pset f hf S ) ≤ μ ( ⋃ l ∈ S, ⋃ a, ⋃ ( _ : a ≤ b ), f '' Cyl ( phi f hf ( a :: l ) ) ) + ε ∧ μ ( ⋃ l ∈ S, ⋃ a, ⋃ ( _ : a ≤ b ), f '' Cyl ( phi f hf ( a :: l ) ) ) ≤ μ ( Pset f hf S ) + ε› δ hδ ) fun N hN => ⟨ N, hN N le_rfl |>.1 ⟩

variable (ε : ℝ≥0∞) (hε : 0 < ε)

include hε

/-- The surviving codes at generation `n`. -/
noncomputable def Surv : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | (n + 1) =>
      nextSurv (Surv n)
        (Classical.choose
          (exists_bound f hf μ (Surv n) (ε * (1 / 2) ^ (n + 1))
            (ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by norm_num)))))

theorem Surv_zero : Surv f hf μ ε hε 0 = {[]} := rfl

theorem Surv_succ (n : ℕ) :
    μ (Pset f hf (Surv f hf μ ε hε n)) ≤
      μ (Pset f hf (Surv f hf μ ε hε (n + 1))) + ε * (1 / 2) ^ (n + 1) := by
  have h := Classical.choose_spec
    (exists_bound f hf μ (Surv f hf μ ε hε n) (ε * (1 / 2) ^ (n + 1))
      (ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by norm_num))))
  exact h

theorem Pset_Surv_zero : Pset f hf (Surv f hf μ ε hε 0) = range f := by
  rw [Surv_zero, Pset]
  simp only [Finset.mem_singleton, iUnion_iUnion_eq_left]
  rw [phi_nil, Cyl_nil, image_univ]

/-
Each code in `Surv n` has length `n`.
-/
theorem Surv_length (n : ℕ) : ∀ l ∈ Surv f hf μ ε hε n, l.length = n := by
  induction' n with n ih;
  · simp +decide [ Surv_zero ];
  · intro l hl; rw [Surv] at hl; simp_all +decide [ Finset.mem_biUnion, Finset.mem_image ] ;
    unfold nextSurv at hl; aesop;

/-
`Bset ∘ Surv` is antitone.
-/
theorem Bset_Surv_antitone (n : ℕ) :
    Bset f hf (Surv f hf μ ε hε (n + 1)) ⊆ Bset f hf (Surv f hf μ ε hε n) := by
  rw [Surv];
  simp +decide [ Bset, nextSurv ];
  exact fun l hl a ha => Set.subset_iUnion₂_of_subset l hl ( Asc_antitone f hf a l )

/-
Telescoped measure bound: the range is captured up to `ε` by every closed truncation.
-/
theorem range_le_Bset (n : ℕ) :
    μ (range f) ≤ μ (Bset f hf (Surv f hf μ ε hε n)) + ε := by
  -- By induction on $n$, we can show that $\mu(\text{range } f) \leq \mu(P_n) + \sum_{k=0}^{n-1} \epsilon \cdot (1/2)^{k+1}$.
  have h_ind : ∀ n, μ (Set.range f) ≤ μ (Pset f hf (Surv f hf μ ε hε n)) + ∑ k ∈ Finset.range n, ε * (1 / 2 : ℝ≥0∞) ^ (k + 1) := by
    intro n;
    induction' n with n ih;
    · simp +decide [ Pset_Surv_zero ];
    · rw [ Finset.sum_range_succ ];
      have := Surv_succ f hf μ ε hε n;
      rw [ ← add_assoc ];
      refine' le_trans ih _;
      rw [ add_right_comm ] ; gcongr;
  refine' le_trans ( h_ind n ) ( add_le_add _ _ );
  · exact MeasureTheory.measure_mono ( Pset_subset_Bset f hf _ );
  · rw [ ← Finset.mul_sum _ _ _ ];
    refine' mul_le_of_le_one_right hε.le _;
    norm_num [ pow_succ', ← mul_assoc, ← Finset.mul_sum _ _ _, ENNReal.tsum_mul_left ];
    rw [ ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ENNReal.toReal_sum ];
      · norm_num [ ENNReal.toReal_pow ];
        rw [ geom_sum_eq ] <;> ring <;> norm_num;
      · exact fun _ _ => ENNReal.pow_ne_top ( by norm_num );
    · exact ENNReal.mul_ne_top ( by norm_num ) ( ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.pow_ne_top ( by norm_num ) )

/-
For every code in `Surv n` (with `n ≥ 1`), the attached closed set has small diameter.
-/
theorem Asc_diam_Surv (n : ℕ) (hn : 1 ≤ n) :
    ∀ l ∈ Surv f hf μ ε hε n, Metric.ediam (Asc f hf l) ≤ ENNReal.ofReal ((1 / 2) ^ n) := by
  intro l hl
  have h_len : l.length = n := by
    grind +suggestions
  generalize_proofs at *;
  rcases l with ( _ | ⟨ a, l ⟩ ) <;> simp_all +decide;
  · linarith;
  · have := Asc_diam f hf a l;
    convert mul_le_mul_right' this ( 2 ^ n ) using 1 ; norm_num [ ← h_len, ENNReal.ofReal_pow ];
    rw [ ← mul_pow, ENNReal.ofReal_div_of_pos ] <;> norm_num;
    rw [ ENNReal.inv_mul_cancel ] <;> norm_num

/-- The truncation level chosen at generation `n`. -/
noncomputable def survBound (n : ℕ) : ℕ :=
  Classical.choose
    (exists_bound f hf μ (Surv f hf μ ε hε n) (ε * (1 / 2) ^ (n + 1))
      (ENNReal.mul_pos hε.ne' (pow_ne_zero _ (by norm_num))))

theorem Surv_succ_eq (n : ℕ) :
    Surv f hf μ ε hε (n + 1) = nextSurv (Surv f hf μ ε hε n) (survBound f hf μ ε hε n) := rfl

theorem mem_nextSurv_cons {S : Finset (List ℕ)} {m a : ℕ} {l : List ℕ} :
    a :: l ∈ nextSurv S m ↔ l ∈ S ∧ a ≤ m := by
  unfold nextSurv; aesop;

theorem tail_mem_Surv (n a : ℕ) (l : List ℕ)
    (h : a :: l ∈ Surv f hf μ ε hε (n + 1)) : l ∈ Surv f hf μ ε hε n := by
  grind +suggestions

/-
Codes surviving at generation `n` have all their entries bounded by the chosen levels.
-/
theorem entry_le_survBound (n : ℕ) (α : ℕ → ℕ)
    (h : res α n ∈ Surv f hf μ ε hε n) : ∀ k, k < n → α k ≤ survBound f hf μ ε hε k := by
  induction' n with n ih generalizing α;
  · tauto;
  · grind +suggestions

/-- The limiting compact set. -/
def Kset : Set X := ⋂ n, Bset f hf (Surv f hf μ ε hε n)

theorem isClosed_Kset : IsClosed (Kset f hf μ ε hε) :=
  isClosed_iInter (fun _ => isClosed_Bset f hf _)

theorem totallyBounded_Kset : TotallyBounded (Kset f hf μ ε hε) := by
  rw [ Metric.totallyBounded_iff ];
  intro δ hδ_pos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 ≤ n ∧ (1 / 2 : ℝ) ^ n < δ := by
    obtain ⟨ n, hn ⟩ := exists_pow_lt_of_lt_one hδ_pos one_half_lt_one;
    exact ⟨ n + 1, Nat.succ_pos _, lt_of_le_of_lt ( pow_le_pow_of_le_one ( by norm_num ) ( by norm_num ) ( Nat.le_succ _ ) ) hn ⟩;
  refine' ⟨ _, _, _ ⟩;
  exact Set.image ( fun l => Classical.choose ( Asc_nonempty f hf l ) ) ( Surv f hf μ ε hε n |> Finset.toSet );
  · exact Set.Finite.image _ ( Finset.finite_toSet _ );
  · intro x hx
    have hx_Bset : x ∈ Bset f hf (Surv f hf μ ε hε n) := by
      exact Set.mem_iInter.mp hx n
    simp_all +decide [ Bset ];
    obtain ⟨ l, hl₁, hl₂ ⟩ := hx_Bset
    have h_dist : dist x (Classical.choose ( Asc_nonempty f hf l )) ≤ ENNReal.toReal ( Metric.ediam ( Asc f hf l ) ) := by
      have h_dist : edist x (Classical.choose ( Asc_nonempty f hf l )) ≤ Metric.ediam ( Asc f hf l ) := by
        exact Metric.edist_le_ediam_of_mem hl₂ ( Classical.choose_spec ( Asc_nonempty f hf l ) )
      generalize_proofs at *;
      convert ENNReal.toReal_mono _ h_dist using 1 <;> norm_num [ edist_dist ];
      exact ne_of_lt ( lt_of_le_of_lt ( Asc_diam_Surv f hf μ ε hε n hn.1 l hl₁ ) ( ENNReal.ofReal_lt_top ) )
    generalize_proofs at *;
    have h_dist_lt : Metric.ediam (Asc f hf l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      exact Asc_diam_Surv f hf μ ε hε n hn.1 l hl₁
    generalize_proofs at *;
    refine' ⟨ l, hl₁, lt_of_le_of_lt h_dist _ ⟩
    generalize_proofs at *;
    exact lt_of_le_of_lt ( ENNReal.toReal_mono ( by aesop ) h_dist_lt ) ( by simpa using hn.2 )

theorem isCompact_Kset : IsCompact (Kset f hf μ ε hε) :=
  (totallyBounded_Kset f hf μ ε hε).isCompact_of_isClosed (isClosed_Kset f hf μ ε hε)

theorem Kset_subset_range : Kset f hf μ ε hε ⊆ range f := by
  intro x hx
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℕ, ∀ n, res β n ∈ Surv f hf μ ε hε n ∧ x ∈ Asc f hf (res β n) := by
    set b : ℕ → ℕ := fun k => survBound f hf μ ε hε k
    set 𝒦 : Set (ℕ → ℕ) := {α | ∀ k, α k ≤ b k};
    set F : ℕ → Set (ℕ → ℕ) := fun n => {α | res α n ∈ Surv f hf μ ε hε n ∧ x ∈ Asc f hf (res α n)} ∩ 𝒦;
    have hF_nonempty : ∀ n, (F n).Nonempty := by
      intro n
      obtain ⟨l, hl⟩ : ∃ l ∈ Surv f hf μ ε hε n, x ∈ Asc f hf l := by
        have := Set.mem_iInter.mp hx n; simp_all +decide [ Bset ] ;
      generalize_proofs at *;
      -- Define `α₀` such that `α₀ k = extend l k` for `k < n` and `α₀ k = 0` for `k ≥ n`.
      set α₀ : ℕ → ℕ := fun k => if k < n then extend l k else 0
      generalize_proofs at *;
      use α₀
      generalize_proofs at *;
      simp [α₀, F];
      refine' ⟨ ⟨ _, _ ⟩, _ ⟩
      all_goals generalize_proofs at *;
      · convert hl.1 using 1
        generalize_proofs at *;
        convert res_extend l using 1
        generalize_proofs at *;
        convert res_congr _ _ _ _ using 1
        generalize_proofs at *;
        rotate_left;
        exact fun k => extend l k
        all_goals generalize_proofs at *;
        · exact fun i hi => if_pos hi;
        · have := Surv_length f hf μ ε hε n l hl.1; aesop;
      · convert hl.2 using 1
        generalize_proofs at *;
        congr! 1
        generalize_proofs at *;
        convert res_extend l using 1
        generalize_proofs at *;
        convert res_congr _ _ _ _ using 1
        generalize_proofs at *;
        rotate_left;
        exact fun k => extend l k
        all_goals generalize_proofs at *;
        · exact fun i hi => if_pos hi;
        · have := Surv_length f hf μ ε hε n l hl.1; aesop;
      · intro k; by_cases hk : k < n <;> simp +decide [ hk ] ;
        convert entry_le_survBound f hf μ ε hε n ( extend l ) _ k hk using 1
        generalize_proofs at *;
        convert hl.1 using 1
        generalize_proofs at *;
        convert res_extend l using 1
        generalize_proofs at *;
        have := Surv_length f hf μ ε hε n l hl.1; aesop;;
    have hF_closed : ∀ n, IsClosed (F n) := by
      intro n
      have hF_closed : IsClosed {α : ℕ → ℕ | res α n ∈ Surv f hf μ ε hε n ∧ x ∈ Asc f hf (res α n)} := by
        have hF_closed : ∀ l ∈ Surv f hf μ ε hε n, IsClosed {α : ℕ → ℕ | res α n = l ∧ x ∈ Asc f hf l} := by
          intro l hl
          have hF_closed : IsClosed {α : ℕ → ℕ | res α n = l} := by
            convert isClosed_Cyl l using 1
            generalize_proofs at *;
            grind +suggestions
          generalize_proofs at *;
          by_cases h : x ∈ Asc f hf l <;> simp +decide [ h, hF_closed ]
        generalize_proofs at *;
        convert isClosed_biUnion_finset fun l hl => hF_closed l hl using 1
        generalize_proofs at *;
        ext α; simp [Set.mem_iUnion]
      generalize_proofs at *;
      exact hF_closed.inter ( isClosed_Iic.preimage <| continuous_pi fun _ => continuous_apply _ );
    have hF_antitone : Antitone F := by
      refine' antitone_nat_of_succ_le _;
      intro n α hα
      obtain ⟨hα_surv, hα_𝒦⟩ := hα
      generalize_proofs at *;
      exact ⟨ ⟨ tail_mem_Surv f hf μ ε hε n _ _ hα_surv.1, hα_surv.2 |> fun h => Asc_antitone f hf _ _ h ⟩, hα_𝒦 ⟩;
    have hF_inter_nonempty : (⋂ n, F n).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed;
      · exact fun n => hF_antitone n.le_succ;
      · exact hF_nonempty;
      · have hF_compact : IsCompact 𝒦 := by
          exact isCompact_pi_infinite fun k => Set.finite_Iic _ |> Set.Finite.isCompact;
        exact hF_compact.of_isClosed_subset ( hF_closed 0 ) fun x hx => hx.2;
      · exact hF_closed;
    obtain ⟨β, hβ⟩ := hF_inter_nonempty;
    use β;
    intro n;
    aesop;
  generalize_proofs at *;
  exact mem_range_of_branch f hf x β (fun n => hβ n |>.2)

theorem range_le_Kset : μ (range f) ≤ μ (Kset f hf μ ε hε) + ε := by
  by_contra h_neg;
  -- Apply the continuity from above property of measures to the sequence `Bset f hf (Surv f hf μ ε hε n)`.
  have h_cont_above : Filter.Tendsto (fun n => μ (Bset f hf (Surv f hf μ ε hε n))) Filter.atTop (nhds (μ (⋂ n, Bset f hf (Surv f hf μ ε hε n)))) := by
    apply_rules [ MeasureTheory.tendsto_measure_iInter_atTop ];
    · exact fun n => MeasurableSet.nullMeasurableSet ( measurableSet_Bset f hf _ );
    · exact antitone_nat_of_succ_le fun n => Bset_Surv_antitone f hf μ ε hε n;
    · exact ⟨ 0, ne_of_lt ( MeasureTheory.measure_lt_top _ _ ) ⟩;
  exact h_neg <| le_of_tendsto_of_tendsto' tendsto_const_nhds ( h_cont_above.add_const ε ) fun n => range_le_Bset f hf μ ε hε n

/-! ## Main auxiliary theorem -/

theorem choquet_core_aux :
    ∃ K, IsCompact K ∧ K ⊆ range f ∧ μ (range f) ≤ μ K + ε :=
  ⟨Kset f hf μ ε hε, isCompact_Kset f hf μ ε hε, Kset_subset_range f hf μ ε hε,
    range_le_Kset f hf μ ε hε⟩

end ChoquetAux

namespace LeanFormalizations.Capacitability

/-! ## The Souslin scheme of a continuous map out of Baire space -/

/-- The Souslin scheme of a continuous map out of Baire space: `cylImg f σ n = f '' cylinder σ n`, the
continuous image of the length-`n` cylinder based at `σ`. -/
def cylImg {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) (n : ℕ) : Set X :=
  f '' PiNat.cylinder (E := fun _ => ℕ) σ n

/-- The root of the scheme is the whole range (`cylinder · 0 = univ`). -/
theorem cylImg_zero {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) :
    cylImg f σ 0 = range f := by
  rw [cylImg, PiNat.cylinder_zero, image_univ]

/-- **Regularity of the scheme:** every node is the union of its (countably many) children, obtained by
fixing the `n`-th coordinate. From `PiNat.iUnion_cylinder_update`. -/
theorem cylImg_decomp {X : Type*} (f : (ℕ → ℕ) → X) (σ : ℕ → ℕ) (n : ℕ) :
    cylImg f σ n = ⋃ k, cylImg f (update σ n k) (n + 1) := by
  rw [cylImg, ← PiNat.iUnion_cylinder_update σ n, image_iUnion]
  rfl

/-- Each scheme node is analytic (continuous image of an open cylinder). -/
theorem analyticSet_cylImg {X : Type*} [TopologicalSpace X] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    (σ : ℕ → ℕ) (n : ℕ) : AnalyticSet (cylImg f σ n) :=
  (PiNat.isOpen_cylinder (E := fun _ => ℕ) σ n).analyticSet_image hf

/-! ## Brick A, decomposed: the whole reduction is proven, the sole hole is the finite Choquet core -/

/-- A nonempty analytic set is a continuous image of Baire space `ℕ → ℕ` (from the mathlib
*definition* of `AnalyticSet`, peeling the empty disjunct). -/
theorem analyticSet_exists_range {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : AnalyticSet s) (hne : s.Nonempty) :
    ∃ f : (ℕ → ℕ) → X, Continuous f ∧ range f = s := by
  rw [AnalyticSet] at hs
  rcases hs with h | h
  · exact absurd h hne.ne_empty
  · exact h

/-- The "bounded box" `{α : ℕ → ℕ | ∀ i, α i ≤ b i}` is **compact**: it is the product
`∏ᵢ Iic (b i)` of finite (hence compact) sets, compact by Tychonoff. This is the pruned subtree whose
continuous image is the compact `K` extracted in the Choquet argument. -/
theorem isCompact_setOf_forall_le (b : ℕ → ℕ) :
    IsCompact {α : ℕ → ℕ | ∀ i, α i ≤ b i} := by
  have h : {α : ℕ → ℕ | ∀ i, α i ≤ b i} = Set.univ.pi (fun i => Set.Iic (b i)) := by
    ext α; simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Iic]
  rw [h]
  exact isCompact_univ_pi (fun i => (Set.finite_Iic (b i)).isCompact)

/-- **The finite Choquet core, range form (THE crux; the sole remaining `sorry` of the `jvn` route).**
For a **finite** measure `μ` and a continuous `f : (ℕ→ℕ) → X`, the analytic set `range f` is
inner-approximated by compacts: for `ε > 0` there is a compact `K ⊆ range f` with
`μ (range f) ≤ μ K + ε`. This is the genuine content of Choquet's capacitability theorem (inner
regularity of analytic sets by compacts); see the file header / `PENDING_WORK.md` for the Lusin-scheme
argument (the naive cumulative-bound regularisation has a real diameter-control gap) and the
`brownian-motion` port alternative (the online-research request). -/
theorem choquet_core_range
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {f : (ℕ → ℕ) → X} (hf : Continuous f)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ range f ∧ μ (range f) ≤ μ K + ε := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable X
  exact ChoquetAux.choquet_core_aux f hf μ ε hε

/-- **The finite Choquet core, analytic-set form (PROVEN from the range form).** For a finite measure,
every analytic set is inner-approximated by compacts. Empty case: `K = ∅`. Nonempty case: write
`s = range f` (`analyticSet_exists_range`) and apply `choquet_core_range`. -/
theorem exists_isCompact_subset_outerMeasure_le
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + ε := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, isCompact_empty, Subset.rfl, by simp⟩
  · obtain ⟨f, hf, hfr⟩ := analyticSet_exists_range hs hne
    obtain ⟨K, hKc, hKs, hKμ⟩ := choquet_core_range μ hf hε
    exact ⟨K, hKc, hfr ▸ hKs, by rw [← hfr]; exact hKμ⟩

/-- **Finite-measure capacitability (PROVEN from the core).** For a finite measure, every analytic set
is `μ`-`NullMeasurable`. Build `F = ⋃ₙ Kₙ ⊆ s` from compacts `Kₙ` with `μ s ≤ μ Kₙ + n⁻¹`; then
`μ F = μ s`, and with `G = toMeasurable μ s ⊇ s` (`μ G = μ s`) the sandwich gives `μ (s \ F) = 0`, i.e.
`s =ᵐ[μ] F`. -/
theorem analyticSet_nullMeasurableSet_finite
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {s : Set X} (hs : AnalyticSet s) :
    NullMeasurableSet s μ := by
  -- compact inner approximations `Kₙ ⊆ s` with `μ s ≤ μ Kₙ + n⁻¹`
  have hK : ∀ n : ℕ, ∃ K, IsCompact K ∧ K ⊆ s ∧ μ s ≤ μ K + (↑n)⁻¹ := fun n =>
    exists_isCompact_subset_outerMeasure_le μ hs
      (ε := (↑n)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top n))
  choose K hKc hKs hKμ using hK
  have hFmeas : MeasurableSet (⋃ i, K i) := MeasurableSet.iUnion fun i => (hKc i).measurableSet
  have hFsub : (⋃ i, K i) ⊆ s := iUnion_subset hKs
  -- `μ s ≤ μ (⋃ i, K i)`
  have hμF_ge : μ s ≤ μ (⋃ i, K i) := by
    refine ENNReal.le_of_forall_pos_le_add fun r hr _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.mpr hr.ne')
    calc μ s ≤ μ (K n) + (↑n)⁻¹ := hKμ n
      _ ≤ μ (⋃ i, K i) + (↑n)⁻¹ := add_le_add (measure_mono (subset_iUnion K n)) le_rfl
      _ ≤ μ (⋃ i, K i) + ↑r := add_le_add le_rfl hn.le
  have hμF : μ (⋃ i, K i) = μ s := le_antisymm (measure_mono hFsub) hμF_ge
  -- outer measurable hull `G = toMeasurable μ s ⊇ s` with `μ G = μ s`
  have hsG : s ⊆ toMeasurable μ s := subset_toMeasurable μ s
  have hμG : μ (toMeasurable μ s) = μ s := measure_toMeasurable s
  have hFG : (⋃ i, K i) ⊆ toMeasurable μ s := hFsub.trans hsG
  have hμFlt : μ (⋃ i, K i) ≠ ∞ := by rw [hμF]; exact (measure_lt_top μ s).ne
  -- `μ (s \ F) = 0` via the sandwich `s \ F ⊆ G \ F`, `μ (G \ F) = 0`
  have hdiff : μ (toMeasurable μ s \ ⋃ i, K i) = 0 := by
    rw [measure_diff hFG hFmeas.nullMeasurableSet hμFlt, hμG, hμF, tsub_self]
  have hsF0 : μ (s \ ⋃ i, K i) = 0 := measure_mono_null (diff_subset_diff_left hsG) hdiff
  have hFs0 : μ ((⋃ i, K i) \ s) = 0 := by rw [diff_eq_empty.mpr hFsub]; exact measure_empty
  exact hFmeas.nullMeasurableSet.congr (ae_eq_set.mpr ⟨hsF0, hFs0⟩).symm

/-- **Brick A — capacitability (PROVEN from the finite case via the σ-finite reduction).** For a
σ-finite measure `μ` on a Polish space, every analytic set is `μ`-`NullMeasurable`. The only use here is
`μ = volume` on `ℝ` (σ-finite). Reduction: `s = ⋃ₙ (s ∩ spanningSets μ n)`; on each finite piece the
finite case applies, transferred through `nullMeasurableSet_restrict`; the union is `NullMeasurable`. -/
theorem analyticSet_nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : Set X} (hs : AnalyticSet s) (μ : Measure X) [SigmaFinite μ] : NullMeasurableSet s μ := by
  have hcover : s = ⋃ n, s ∩ spanningSets μ n := by
    rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  rw [hcover]
  refine NullMeasurableSet.iUnion fun n => ?_
  have hDmeas : MeasurableSet (spanningSets μ n) := measurableSet_spanningSets μ n
  have hDfin : μ (spanningSets μ n) ≠ ∞ := (measure_spanningSets_lt_top μ n).ne
  haveI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) := isFiniteMeasure_restrict.mpr hDfin
  have hnm : NullMeasurableSet s (μ.restrict (spanningSets μ n)) :=
    analyticSet_nullMeasurableSet_finite (μ.restrict (spanningSets μ n)) hs
  exact (nullMeasurableSet_restrict hDmeas.nullMeasurableSet).mp hnm

end LeanFormalizations.Capacitability
