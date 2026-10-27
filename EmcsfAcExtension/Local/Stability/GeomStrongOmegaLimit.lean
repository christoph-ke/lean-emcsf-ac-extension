module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Infra.AC.Quotient

/-! # The metric coefficient from uniform geometric limits

The positive mass gap is preserved before the reciprocal is formed.
The explicit rational comparison and the AC quotient rule then recover
the same metric coefficient in both characteristic directions.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Uniform real field convergence gives pointwise convergence at each
triangle point, with no estimate constant or regularity premise. -/
theorem stab_real_field_tendsto_at_point {T : ℝ} {F : ℕ → ℝ → ℝ → ℝ}
    {f : ℝ → ℝ → ℝ}
    (hvalue : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v,
      (u, v) ∈ triangle 0 T → |F k u v - f u v| < δ)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    Tendsto (fun k => F k u v) atTop (𝓝 (f u v)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN⟩ := hvalue δ hδ
  exact ⟨N, fun k hk => by simpa only [Real.dist_eq] using hN k hk u v hp⟩

/-- The fixed expansion bounds and mass gap survive uniform geometric
convergence. The literal bounds `1,1,1/4` are universal and precede all
field parameters and sequences, with no derivative bound involved. -/
theorem stab_geometric_limit_box_c1
    {e T ε M A : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ}
    (hset : ∀ k, StabSetting e T ε M A (Sn k) (hn k))
    {l n mu : ℝ → ℝ → ℝ}
    (hL : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).lam u v - l u v| < δ)
    (hN : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).nu u v - n u v| < δ)
    (hM : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).mu u v - mu u v| < δ) :
    ∀ u v, (u, v) ∈ triangle 0 T →
      |l u v| ≤ 1 ∧ |n u v| ≤ 1 ∧ 1 / 4 ≤ 1 - mu u v := by
  intro u v hp
  have htl := stab_real_field_tendsto_at_point hL hp
  have htn := stab_real_field_tendsto_at_point hN hp
  have htm := stab_real_field_tendsto_at_point hM hp
  refine ⟨le_of_tendsto htl.abs (Eventually.of_forall fun k => ?_),
    le_of_tendsto htn.abs (Eventually.of_forall fun k => ?_),
    ge_of_tendsto (tendsto_const_nhds.sub htm) (Eventually.of_forall fun k => ?_)⟩
  · rw [abs_of_pos ((hset k).c1.lam_pos (u, v) hp)]
    exact ((hset k).box.2 (u, v) hp).2.1
  · rw [abs_of_neg ((hset k).c1.nu_neg (u, v) hp)]
    exact ((hset k).box.2 (u, v) hp).2.2.2.1
  · exact ((hset k).box.2 (u, v) hp).2.2.2.2.1

/-- The metric coefficient `-4νλ/(1-μ)` converges uniformly to the
rational expression in the three geometric limits. The comparison
coefficient `80` is universal; the denominator gap is retained before
passing to the limit, uniformly in all scales and minimum radii. -/
theorem stab_omega_uniform_of_geometric_uniform_c1
    {e T ε M A : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ}
    (hset : ∀ k, StabSetting e T ε M A (Sn k) (hn k))
    {l n mu : ℝ → ℝ → ℝ}
    (hL : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).lam u v - l u v| < δ)
    (hN : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).nu u v - n u v| < δ)
    (hM : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).mu u v - mu u v| < δ) :
    ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ k ≥ N, ∀ u v, (u, v) ∈ triangle 0 T →
      |(Sn k).Omega2 u v - (-4 * n u v * l u v / (1 - mu u v))| < δ := by
  have hbox := stab_geometric_limit_box_c1 hset hL hN hM
  intro δ hδ
  have hδs : 0 < δ / 240 := div_pos hδ (by norm_num)
  obtain ⟨NL, hNL⟩ := hL (δ / 240) hδs
  obtain ⟨NN, hNN⟩ := hN (δ / 240) hδs
  obtain ⟨NM, hNM⟩ := hM (δ / 240) hδs
  refine ⟨max (max NL NN) NM, fun k hk u v hp => ?_⟩
  have hl := hNL k ((le_max_left _ _).trans ((le_max_left _ _).trans hk)) u v hp
  have hn := hNN k ((le_max_right _ _).trans ((le_max_left _ _).trans hk)) u v hp
  have hm := hNM k ((le_max_right _ _).trans hk) u v hp
  have hlim := hbox u v hp
  have hb := (hset k).box.2 (u, v) hp
  have hc := stab_potential_coefficient_sub_le
    (by rw [abs_of_pos ((hset k).c1.lam_pos _ hp)]; exact hb.2.1)
    hlim.1 hlim.2.1 hb.2.2.2.2.1 hlim.2.2 (le_refl
      (|(Sn k).nu u v - n u v| + |(Sn k).lam u v - l u v|))
    (le_refl |(Sn k).mu u v - mu u v|)
  have heq : (Sn k).Omega2 u v - (-4 * n u v * l u v / (1 - mu u v)) =
      -2 * (2 * (Sn k).nu u v * (Sn k).lam u v / (1 - (Sn k).mu u v) -
        2 * n u v * l u v / (1 - mu u v)) := by
    dsimp only [Fields.Omega2]
    ring
  rw [heq, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (40 * (|(Sn k).nu u v - n u v| + |(Sn k).lam u v - l u v| +
        |(Sn k).mu u v - mu u v|)) := mul_le_mul_of_nonneg_left hc (by norm_num)
    _ < 2 * (40 * (δ / 240 + δ / 240 + δ / 240)) := by gcongr
    _ = _ := by ring

/-- The metric quotient of three AC real section functions is AC
under the literal mass gap `1/4`. This is an exact composition result
with no estimate constant or additional variation bound. -/
theorem stab_omega_ac_of_components {a b : ℝ} {l n mu : ℝ → ℝ}
    (hL : AbsolutelyContinuousOnInterval l a b)
    (hN : AbsolutelyContinuousOnInterval n a b)
    (hM : AbsolutelyContinuousOnInterval mu a b)
    (hgap : ∀ x ∈ uIcc a b, 1 / 4 ≤ 1 - mu x) :
    AbsolutelyContinuousOnInterval (fun x => -4 * n x * l x / (1 - mu x)) a b := by
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ((hN.const_mul (-4)).mul_normed_ring hL).div_of_le_norm (hconst.sub hM)
    (by norm_num : (0 : ℝ) < 1 / 4) (fun x hx => by
      rw [Real.norm_eq_abs]
      exact (hgap x hx).trans (le_abs_self _))

end EmcsfAcExtension.Local
