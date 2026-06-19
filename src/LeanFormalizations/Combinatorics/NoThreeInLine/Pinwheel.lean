/-
# The HJSW pinwheel: the `3(p−1)` no-three-in-line construction (half-band form)

Hall–Jackson–Sudbery–Wild (J. Combin. Theory Ser. A 18 (1975) 336–341, Theorem 2) realize
`3(p−1)` no-three-in-line points in the `2p × 2p` grid — density `3/2`, the best *proven* constant.

## ⚠️ Why the construction is the *half-band* one (and not the naïve `{0,p}²` corners)

An earlier attempt kept three of the four `{0,p}²`-translates `(a,b),(a+p,b),(a,b+p),(a+p,b+p)` of
each residue class, dropping one corner. **That set is no-three-in-line for NO drop rule** (brute-forced
INFEASIBLE at `p = 7` for every `k`): the symmetric corner layout couples each class to a slope-`+1`
partner *and* a slope-`−1` partner at once, forcing both diagonals of the class to be broken — which a
single drop cannot do. The genuine HJSW construction breaks this symmetry with a **half-band shift**.

For each nonzero residue `a ∈ [1,p)` put `b = (k·a⁻¹) mod p ∈ [1,p)`. With `h = (p−1)/2`:
* the **outer** column sits at `x = a + h`;
* the **inner** column sits at `x = a + h + p` when `a ≤ h` (left half) or `x = a + h − p` when `a > h`
  (right half) — i.e. the `±p` translate always points *toward the centre*;
* the rows are `y = b` and `y = b + p`.
The kept three points are the **whole inner column** `(inner, b), (inner, b+p)` plus the **outer corner
on `b`'s own side** — `(outer, b+p)` if `b` is in the upper half (`h < b`), else `(outer, b)`. (The
global `+h` shift in `x` lands the figure in `[0,2p)²`; it is a single translation, so it preserves
every collinearity.) This is HJSW Figure I read class-by-class instead of family-by-family.

## What is mechanical vs. the crux
`pinwheel_card = 3(p−1)` and `pinwheel_grid ⊆ [0,2p)²` are mechanical (proved below). The crux is
`pinwheel_noThree`. Reductions, all but the last proved here:
* every kept point lies on the sheared hyperbola `(x − h)·y ≡ k` (`pinKeep_rel`); the general HJSW
  Lemma then gives, for any collinear triple, two points of one residue class
  (`pinwheel_collinear_same_xres`, via the `det3` collapse sheared by `−h`);
* slope `0`/`∞` are automatically safe — each row/column meets a single class (`pinwheel_eq_*`);
* the **same-class** subcase is impossible — the three kept points of a class form a right triangle of
  area `p²/2` (`pinKeep_not_collinear`);
* the surviving danger is the **cross-class slope-`±1`** incidence: the two classes on such a line are
  σ-reflections (`hyperbola_slope_one_reflection` / `_neg_one_reflection`), and HJSW's family layout
  puts the partner's three points on lines offset by exactly `±p` from the diagonal, so none is on it.
-/
import LeanFormalizations.Combinatorics.NoThreeInLine.HyperbolaLine
import LeanFormalizations.Combinatorics.NoThreeInLine.UpperBound

namespace LeanFormalizations.NoThreeInLine

open Finset

/-! ### The half-width `h = (p−1)/2` and the column abscissae -/

/-- Half-width `h = (p−1)/2`. For odd `p`, `2h + 1 = p`. -/
def pinH (p : ℕ) : ℕ := (p - 1) / 2

/-- For odd `p`, `2·((p−1)/2) + 1 = p`. -/
theorem two_mul_pinH_add_one {p : ℕ} (hp : Odd p) : 2 * pinH p + 1 = p := by
  obtain ⟨m, rfl⟩ := hp; unfold pinH; omega

/-- The outer-column abscissa of class `a` (shifted into `[0,2p)`): `a + h`. -/
def pinOuterX (p a : ℕ) : ℕ := a + pinH p

/-- The inner-column abscissa: `a + h + p` if `a ≤ h` (left half), else `a + h − p` (right half). -/
def pinInnerX (p a : ℕ) : ℕ := if a ≤ pinH p then a + pinH p + p else a + pinH p - p

theorem pinOuterX_cast {p a : ℕ} :
    (pinOuterX p a : ZMod p) = (a : ZMod p) + (pinH p : ZMod p) := by
  unfold pinOuterX; push_cast; ring

theorem pinInnerX_cast {p a : ℕ} (hp : Odd p) (_ha : a < p) :
    (pinInnerX p a : ZMod p) = (a : ZMod p) + (pinH p : ZMod p) := by
  have h2 := two_mul_pinH_add_one hp
  unfold pinInnerX
  split
  · push_cast [ZMod.natCast_self]; ring
  · rename_i hr
    rw [Nat.cast_sub (by omega : p ≤ a + pinH p)]
    push_cast [ZMod.natCast_self]; ring

theorem pinOuterX_lt {p a : ℕ} (hp : Odd p) (ha : a < p) : pinOuterX p a < 2 * p := by
  have h2 := two_mul_pinH_add_one hp; unfold pinOuterX; omega

theorem pinInnerX_lt {p a : ℕ} (hp : Odd p) (ha : a < p) : pinInnerX p a < 2 * p := by
  have h2 := two_mul_pinH_add_one hp; unfold pinInnerX; split <;> omega

/-- The two columns of a class are distinct (they differ by `p`). -/
theorem pinOuterX_ne_pinInnerX {p a : ℕ} (hp : Odd p) : pinOuterX p a ≠ pinInnerX p a := by
  have h2 := two_mul_pinH_add_one hp; unfold pinOuterX pinInnerX; split <;> omega

/-! ### The kept point set of a class, the pinwheel, count and grid -/

/-- The three kept points of residue class `a` (`b = hyperbolaY p k a`): the whole inner column,
plus the outer corner on `b`'s own half-band. -/
def pinKeep (p k a : ℕ) : Finset (ℕ × ℕ) :=
  {(pinInnerX p a, hyperbolaY p k a), (pinInnerX p a, hyperbolaY p k a + p),
    (pinOuterX p a, if pinH p < hyperbolaY p k a then hyperbolaY p k a + p else hyperbolaY p k a)}

/-- **The HJSW pinwheel point set**: three points of each nonzero residue class. -/
def pinwheel (p k : ℕ) : Finset (ℕ × ℕ) := (Finset.Ico 1 p).biUnion (pinKeep p k)

private theorem res_ne_zero {p r : ℕ} (hr1 : 1 ≤ r) (hr2 : r < p) : (r : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; have := Nat.le_of_dvd hr1 hd; omega

/-- Each kept set has exactly three points. -/
theorem pinKeep_card {p k a : ℕ} (hp : Odd p) : (pinKeep p k a).card = 3 := by
  have hco := pinOuterX_ne_pinInnerX (p := p) (a := a) hp
  have h2 := two_mul_pinH_add_one hp
  unfold pinKeep
  rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or]
        refine ⟨fun h => ?_, fun h => hco h.1.symm⟩
        omega),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton, Prod.mk.injEq]
        exact fun h => hco h.1.symm),
      Finset.card_singleton]

/-- The `x`-residue of any kept point of class `a` is `a + h`. -/
theorem pinKeep_xres {p k a : ℕ} (hp : Odd p) (ha : a < p) {x : ℕ × ℕ}
    (hx : x ∈ pinKeep p k a) : (x.1 : ZMod p) = (a : ZMod p) + (pinH p : ZMod p) := by
  unfold pinKeep at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact pinInnerX_cast hp ha
  · exact pinInnerX_cast hp ha
  · exact pinOuterX_cast

/-- The `y`-residue of any kept point of class `a` is `b = hyperbolaY p k a`. -/
theorem pinKeep_yres {p k a : ℕ} {x : ℕ × ℕ} (hx : x ∈ pinKeep p k a) :
    (x.2 : ZMod p) = (hyperbolaY p k a : ZMod p) := by
  unfold pinKeep at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rfl
  · push_cast [ZMod.natCast_self]; ring
  · split <;> push_cast [ZMod.natCast_self] <;> ring

/-- Distinct residues give disjoint kept sets (the `x`-residue `a + h` determines `a`). -/
theorem pinKeep_disjoint {p k : ℕ} (hp : Odd p) {a b : ℕ}
    (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    Disjoint (pinKeep p k a) (pinKeep p k b) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have e1 := pinKeep_xres hp ha hxa
  have e2 := pinKeep_xres hp hb hxb
  have he : (a : ZMod p) = (b : ZMod p) := add_right_cancel (e1.symm.trans e2)
  have : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp he
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hab this

/-- **The pinwheel has `3(p−1)` points.** Three kept points per class, `p−1` disjoint classes. -/
theorem pinwheel_card {p k : ℕ} (hp : Odd p) (_hp1 : 0 < p) :
    (pinwheel p k).card = 3 * (p - 1) := by
  unfold pinwheel
  rw [Finset.card_biUnion (fun a ha b hb hab =>
        pinKeep_disjoint hp (Finset.mem_Ico.mp ha).2 (Finset.mem_Ico.mp hb).2 hab)]
  rw [Finset.sum_congr rfl (fun a _ => pinKeep_card hp)]
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega

/-- **The pinwheel lies in the `2p × 2p` grid.** -/
theorem pinwheel_grid {p k : ℕ} (hp : Odd p) (hp1 : 0 < p) :
    IsGridSet (2 * p) (pinwheel p k) := by
  haveI : NeZero p := ⟨hp1.ne'⟩
  intro x hx
  unfold pinwheel at hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  rw [Finset.mem_Ico] at ha
  have hya : hyperbolaY p k a < p := ZMod.val_lt _
  have hox := pinOuterX_lt hp ha.2
  have hix := pinInnerX_lt hp ha.2
  unfold pinKeep at hxa
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxa
  rcases hxa with rfl | rfl | rfl
  · exact ⟨hix, by omega⟩
  · exact ⟨hix, by omega⟩
  · exact ⟨hox, by split <;> omega⟩

/-! ### Membership + hyperbola-relation plumbing -/

/-- A pinwheel point is a kept point of some nonzero residue class. -/
theorem mem_pinwheel {p k : ℕ} {x : ℕ × ℕ} (hx : x ∈ pinwheel p k) :
    ∃ a, 1 ≤ a ∧ a < p ∧ x ∈ pinKeep p k a := by
  unfold pinwheel at hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  rw [Finset.mem_Ico] at ha
  exact ⟨a, ha.1, ha.2, hxa⟩

/-- Every kept point lies on the **sheared** hyperbola `(x − h)·y ≡ k (mod p)`. (Unshifting the
`+h` translate recovers the original residue `a`, and `a·b ≡ k`.) -/
theorem pinKeep_rel {p k a : ℕ} [Fact p.Prime] (hp : Odd p) (ha1 : 1 ≤ a) (ha2 : a < p)
    {x : ℕ × ℕ} (hx : x ∈ pinKeep p k a) :
    ((x.1 : ZMod p) - (pinH p : ZMod p)) * (x.2 : ZMod p) = (k : ZMod p) := by
  rw [pinKeep_xres hp ha2 hx, pinKeep_yres hx, add_sub_cancel_right]
  exact hyperbola_xy_eq (res_ne_zero ha1 ha2)

/-- **The sheared HJSW collapse.** Three points on the sheared hyperbola `(x − h)·y ≡ k`, collinear
over `ℝ`, have two equal `x`-residues. (The `−h` shear cancels in every coordinate difference, so the
determinant collapse is the unsheared one applied to `u = x − h`.) -/
theorem sheared_line_x_residue_eq {p k h : ℕ} [Fact p.Prime] (hk : (k : ZMod p) ≠ 0)
    {Xa Ya Xb Yb Xc Yc : ℕ}
    (rA : ((Xa : ZMod p) - h) * (Ya : ZMod p) = k)
    (rB : ((Xb : ZMod p) - h) * (Yb : ZMod p) = k)
    (rC : ((Xc : ZMod p) - h) * (Yc : ZMod p) = k)
    (hcol : Collinear ℝ ({toReal (Xa, Ya), toReal (Xb, Yb), toReal (Xc, Yc)} : Set (ℝ × ℝ))) :
    (Xa : ZMod p) = Xb ∨ (Xa : ZMod p) = Xc ∨ (Xb : ZMod p) = Xc := by
  have hdet := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hdet
  have hZ : ((Xb : ℤ) - Xa) * ((Yc : ℤ) - Ya) - ((Xc : ℤ) - Xa) * ((Yb : ℤ) - Ya) = 0 := by
    exact_mod_cast hdet
  have hcast := congrArg (Int.cast : ℤ → ZMod p) hZ
  push_cast at hcast
  set ua : ZMod p := (Xa : ZMod p) - h with hua
  set ub : ZMod p := (Xb : ZMod p) - h with hub
  set uc : ZMod p := (Xc : ZMod p) - h with huc
  -- collapse: `k·(ua−ub)(ua−uc)(ub−uc) = 0`
  have key : (k : ZMod p) * ((ua - ub) * (ua - uc) * (ub - uc)) = 0 := by
    rw [hua, hub, huc]
    linear_combination
        (-((Xa : ZMod p) - h) * ((Xb : ZMod p) - h) * ((Xc : ZMod p) - h)) * hcast
      + (((Xb : ZMod p) - h) * ((Xc : ZMod p) - h) * (((Xc : ZMod p) - h) - ((Xb : ZMod p) - h))) * rA
      - (((Xa : ZMod p) - h) * ((Xc : ZMod p) - h) * (((Xc : ZMod p) - h) - ((Xa : ZMod p) - h))) * rB
      + (((Xa : ZMod p) - h) * ((Xb : ZMod p) - h) * (((Xb : ZMod p) - h) - ((Xa : ZMod p) - h))) * rC
  have prod := (mul_eq_zero.mp key).resolve_left hk
  have huv : ∀ {u v : ZMod p}, u - v = 0 → (u + h : ZMod p) = v + h := fun h0 => by
    have := sub_eq_zero.mp h0; rw [this]
  rcases mul_eq_zero.mp prod with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · left;  have := huv (u := ua) (v := ub) h1; simpa [hua, hub, sub_add_cancel] using this
    · right; left;  have := huv (u := ua) (v := uc) h2; simpa [hua, huc, sub_add_cancel] using this
  · right; right; have := huv (u := ub) (v := uc) h3; simpa [hub, huc, sub_add_cancel] using this

/-- **The reduction entry point.** Any collinear pinwheel triple has two points in the same residue
class (equal `x`-residue). -/
theorem pinwheel_collinear_same_xres {p k : ℕ} (hp : p.Prime) (hodd : Odd p) (hk : (k : ZMod p) ≠ 0)
    {P Q R : ℕ × ℕ}
    (hP : P ∈ pinwheel p k) (hQ : Q ∈ pinwheel p k) (hR : R ∈ pinwheel p k)
    (hcol : Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ))) :
    (P.1 : ZMod p) = Q.1 ∨ (P.1 : ZMod p) = R.1 ∨ (Q.1 : ZMod p) = R.1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha1, ha2, hPa⟩ := mem_pinwheel hP
  obtain ⟨b, hb1, hb2, hQb⟩ := mem_pinwheel hQ
  obtain ⟨c, hc1, hc2, hRc⟩ := mem_pinwheel hR
  exact sheared_line_x_residue_eq hk
    (pinKeep_rel hodd ha1 ha2 hPa) (pinKeep_rel hodd hb1 hb2 hQb)
    (pinKeep_rel hodd hc1 hc2 hRc) hcol

/-- Equal `x`-residue means equal class: `(P.1 : ZMod p) = Q.1` forces `a = b` for the classes. -/
theorem pinKeep_xres_eq_class {p k : ℕ} (hp : Odd p) {a b : ℕ} (ha : a < p) (hb : b < p)
    {P Q : ℕ × ℕ} (hP : P ∈ pinKeep p k a) (hQ : Q ∈ pinKeep p k b)
    (h : (P.1 : ZMod p) = (Q.1 : ZMod p)) : a = b := by
  have e1 := pinKeep_xres hp ha hP
  have e2 := pinKeep_xres hp hb hQ
  have he : (a : ZMod p) = (b : ZMod p) := add_right_cancel (e1.symm.trans (h.trans e2))
  have : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp he
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ### The crux: the pinwheel is no-three-in-line -/

/-- **The same-class subcase is impossible.** The three kept points of a class are the inner column
`(inner, b), (inner, b+p)` and one outer corner — a right triangle of area `p²/2 ≠ 0`. -/
theorem pinKeep_not_collinear {p k a : ℕ} (hp : Odd p) (_ha : a < p) {P Q R : ℕ × ℕ}
    (hP : P ∈ pinKeep p k a) (hQ : Q ∈ pinKeep p k a) (hR : R ∈ pinKeep p k a)
    (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    ¬ Collinear ℝ ({toReal P, toReal Q, toReal R} : Set (ℝ × ℝ)) := by
  have h2 := two_mul_pinH_add_one hp
  have hco := pinOuterX_ne_pinInnerX (p := p) (a := a) hp
  have hp' : (0 : ℝ) < (p : ℝ) := by have : 0 < p := by omega
                                     exact_mod_cast this
  -- `p ≠ 0` in ℝ for the determinant bound
  have hpR : ((pinInnerX p a : ℝ) - pinOuterX p a) ^ 2 = (p : ℝ) ^ 2 := by
    have : pinInnerX p a = pinOuterX p a + p ∨ pinOuterX p a = pinInnerX p a + p := by
      unfold pinInnerX pinOuterX; split <;> omega
    rcases this with h | h <;> rw [h] <;> push_cast <;> ring
  intro hcol
  have hd := collinear_imp_det3_zero hcol
  simp only [toReal, det3] at hd
  unfold pinKeep at hP hQ hR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP hQ hR
  -- enumerate the three kept points; the inner-column pair is always two of P,Q,R
  rcases hP with rfl | rfl | rfl <;> rcases hQ with rfl | rfl | rfl <;> rcases hR with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hPQ
      | exact absurd rfl hPR
      | exact absurd rfl hQR
      | (revert hd; push_cast; split <;> intro hd <;>
          nlinarith [hd, hpR, hp', mul_pos hp' hp', mul_pos (mul_pos hp' hp') (mul_pos hp' hp'),
            sq_nonneg ((pinInnerX p a : ℝ) - pinOuterX p a)])

/-- **Slope-`0` safety.** Two pinwheel points sharing a `y`-coordinate are in the same class (the
`y`-residue determines the class via `s ↦ a = k·s⁻¹`). -/
theorem pinwheel_eq_snd_same_xres {p k : ℕ} (hp : p.Prime) (hodd : Odd p) (hk : (k : ZMod p) ≠ 0)
    {P Q : ℕ × ℕ} (hP : P ∈ pinwheel p k) (hQ : Q ∈ pinwheel p k) (hsnd : P.2 = Q.2) :
    (P.1 : ZMod p) = (Q.1 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha1, ha2, hPa⟩ := mem_pinwheel hP
  obtain ⟨b, hb1, hb2, hQb⟩ := mem_pinwheel hQ
  have hy : (hyperbolaY p k a : ZMod p) = (hyperbolaY p k b : ZMod p) := by
    rw [← pinKeep_yres hPa, ← pinKeep_yres hQb, hsnd]
  have hab : a = b := by
    have hres := hyperbolaY_inj_residue hk (res_ne_zero ha1 ha2) (res_ne_zero hb1 hb2) ?_
    · have : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).mp hres
      rwa [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at this
    · -- hyperbolaY equal as naturals from equal residues + both `< p`
      have ha' : hyperbolaY p k a < p := ZMod.val_lt _
      have hb' : hyperbolaY p k b < p := ZMod.val_lt _
      have : (hyperbolaY p k a) % p = (hyperbolaY p k b) % p :=
        (ZMod.natCast_eq_natCast_iff' _ _ p).mp hy
      rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at this
  subst hab
  rw [pinKeep_xres hodd ha2 hPa, pinKeep_xres hodd ha2 hQb]

/-- **Slope-`∞` safety** (the column analogue): two points sharing an `x`-coordinate have the same
`x`-residue. -/
theorem pinwheel_eq_fst_same_xres {p : ℕ} {P Q : ℕ × ℕ} (hfst : P.1 = Q.1) :
    (P.1 : ZMod p) = (Q.1 : ZMod p) :=
  congrArg (fun n : ℕ => (n : ZMod p)) hfst

/-- **Crux (disclosed).** The HJSW pinwheel is no-three-in-line. The mechanical scaffolding
(`pinwheel_card`, `pinwheel_grid`), the reduction to two same-class points
(`pinwheel_collinear_same_xres`), the same-class impossibility (`pinKeep_not_collinear`), the slope
`0`/`∞` safety (`pinwheel_eq_*`) and the σ-reflection algebra (`hyperbola_slope_one_reflection` /
`_neg_one_reflection`) are all in place; the remaining content is the cross-class slope-`±1` incidence
— the partner class's three kept points sit on lines offset by exactly `±p` from the diagonal.

This statement is **true** (brute-verified no-three for all primes `p ≤ 17`, every `k`), unlike the
earlier `{0,p}²`-corner construction which was infeasible. -/
theorem pinwheel_noThree {p k : ℕ} (hp : p.Prime) (hodd : Odd p) (hk : (k : ZMod p) ≠ 0) :
    NoThreeCollinear (pinwheel p k) := by
  sorry

/-- **The HJSW `3(p−1)` lower bound (existence form).** For an odd prime `p` the `2p × 2p` grid
carries `3(p−1)` points with no three collinear — modulo the slope-incidence crux `pinwheel_noThree`. -/
theorem hjsw_pinwheel_exists {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ∃ s : Finset (ℕ × ℕ), IsGridSet (2 * p) s ∧ NoThreeCollinear s ∧ s.card = 3 * (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk : ((1 : ℕ) : ZMod p) ≠ 0 := by rw [Nat.cast_one]; exact one_ne_zero
  exact ⟨pinwheel p 1, pinwheel_grid hodd hp.pos, pinwheel_noThree hp hodd hk,
    pinwheel_card hodd hp.pos⟩

/-- **The HJSW `3(p−1)` lower bound** (modulo the crux): `maxNoThreeInLine (2p) ≥ 3(p−1)` for odd
primes `p`. With `p ≈ N/2` this is the `(3/2 − ε)N` constant. -/
theorem three_mul_pred_le_maxNoThreeInLine {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    3 * (p - 1) ≤ maxNoThreeInLine (2 * p) := by
  obtain ⟨s, hg, h3, hc⟩ := hjsw_pinwheel_exists hp hodd
  exact le_csSup (bddAbove_grid (2 * p)) ⟨s, hc.symm, hg, h3⟩

end LeanFormalizations.NoThreeInLine
