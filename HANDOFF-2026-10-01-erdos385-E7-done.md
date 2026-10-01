# Erdős #385 E7 DONE (branch erdos-385-a)

`DensityEES.lean` sorry-free; `F_le_add_sqrt`, `density_one_EES`, `F_sub_div_sqrt_tendsto_one`,
`F_sub_tendsto_atTop` all `#print axioms` = [propext, Classical.choice, Quot.sound] (Richert is a hypothesis).

Key: `density_core` (private). With δ_k = 1/(k+5), B_k increasing, thresholds T k from
`almost_all_F385_of_richert` (density < 1/(k+1)), Y = running sup of T, κ(n) = findGreatest (Y k ≤ n).
E = {n | n ∈ B_{κ n}}; κ monotone ⇒ E ∩ [0,X] ⊆ B_{κ X}, so density ≤ 1/(κ X + 1) → 0. No tail split.
Next: nothing on E7; phase E8 lives on erdos-385-b.

Branch erdos-385-a, HEAD be0efff (+ this note). Run stopped via `box done --green`; scoped target met.
Next steps: none for E7. Merge erdos-385-a into erdos-385 when E8 (erdos-385-b) lands.
