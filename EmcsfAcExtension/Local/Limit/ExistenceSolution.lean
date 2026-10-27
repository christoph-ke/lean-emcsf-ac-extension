module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Limit.ExistenceEquations
import EmcsfAcExtension.Local.Limit.ScalarAxisAC
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Local.Limit.UIAux

/-! # Assembly of the frozen AC integral solution class

The assembly uses characteristic regularity already proved for the primary
limit. It checks the literal frozen clauses, including arbitrary compact
subsegments, all four local BV fields in both directions, and axis traces.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem out_var_le {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → ℝ → E} {T : ℝ} {B : ℝ≥0∞}
    (hvar : ∀ u ∈ Icc 0 T, eVariationOn (f u) (Icc u T) ≤ B)
    {u a b : ℝ} (hseg : outSeg u a b ⊆ triangle 0 T) :
    eVariationOn (f u) (Icc a b) ≤ B := by
  by_cases hab : a ≤ b
  · have ha := hseg (show (u, a) ∈ outSeg u a b from ⟨rfl, le_rfl, hab⟩)
    have hb := hseg (show (u, b) ∈ outSeg u a b from ⟨rfl, hab, le_rfl⟩)
    exact (eVariationOn.mono (f u) (Icc_subset_Icc ha.2.1 hb.2.2)).trans
      (hvar u ⟨ha.1, ha.2.1.trans (hab.trans hb.2.2)⟩)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab), eVariationOn]

private theorem in_var_le {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → ℝ → E} {T : ℝ} {B : ℝ≥0∞}
    (hvar : ∀ v ∈ Icc 0 T, eVariationOn (fun u => f u v) (Icc 0 v) ≤ B)
    {a b v : ℝ} (hseg : inSeg a b v ⊆ triangle 0 T) :
    eVariationOn (fun u => f u v) (Icc a b) ≤ B := by
  by_cases hab : a ≤ b
  · have ha := hseg (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩)
    have hb := hseg (show (b, v) ∈ inSeg a b v from ⟨hab, le_rfl, rfl⟩)
    exact (eVariationOn.mono (fun u => f u v) (Icc_subset_Icc ha.1 hb.2.1)).trans
      (hvar v ⟨ha.1.trans ha.2.1, ha.2.2⟩)
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab), eVariationOn]

private theorem out_ac_mono {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → ℝ → E} {T u a b : ℝ}
    (hf : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T)
    (hab : a ≤ b) (hseg : outSeg u a b ⊆ triangle 0 T) :
    AbsolutelyContinuousOnInterval (f u) a b := by
  have ha := hseg (show (u, a) ∈ outSeg u a b from ⟨rfl, le_rfl, hab⟩)
  have hb := hseg (show (u, b) ∈ outSeg u a b from ⟨rfl, hab, le_rfl⟩)
  apply (hf u ⟨ha.1, ha.2.1.trans (hab.trans hb.2.2)⟩).mono
  rw [uIcc_of_le hab, uIcc_of_le (ha.2.1.trans (hab.trans hb.2.2))]
  exact Icc_subset_Icc ha.2.1 hb.2.2

private theorem in_ac_mono {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → ℝ → E} {T a b v : ℝ}
    (hf : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v)
    (hab : a ≤ b) (hseg : inSeg a b v ⊆ triangle 0 T) :
    AbsolutelyContinuousOnInterval (fun u => f u v) a b := by
  have ha := hseg (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩)
  have hb := hseg (show (b, v) ∈ inSeg a b v from ⟨hab, le_rfl, rfl⟩)
  apply (hf v ⟨ha.1.trans ha.2.1, ha.2.2⟩).mono
  rw [uIcc_of_le hab, uIcc_of_le (ha.1.trans ha.2.1)]
  exact Icc_subset_Icc ha.1 hb.2.1

/-- Assemble the literal frozen solution class after primary limit regularity
has been proved. This helper's finite BV bound `B` may depend on the fixed
configuration and triangle, uniformly in all sections and compact subsets,
as the local BV clause permits. No frozen clause is omitted or weakened. -/
theorem StrongLimit.isSolution_of_characteristic_regularity {e T : ℝ}
    {Sn : ℕ → Fields} {S : Fields} {B : ℝ≥0∞}
    (hT : 0 < T) (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hMu : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mu)
      (Function.uncurry S.mu) atTop (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ triangle 0 T, 0 < 1 - S.mu p.1 p.2)
    (hro : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.r u) u T)
    (hri : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.r u v) 0 v)
    (hmo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.m u) u T)
    (hmi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.m u v) 0 v)
    (hQo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.Q u) u T)
    (hQi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.Q u v) 0 v)
    (hpo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.phi u) u T)
    (hpi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.phi u v) 0 v)
    (hao : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T)
    (hB : B ≠ ⊤)
    (hvo : ∀ u ∈ Icc 0 T, eVariationOn (S.lam u) (Icc u T) ≤ B ∧
      eVariationOn (S.nu u) (Icc u T) ≤ B ∧ eVariationOn (S.a u) (Icc u T) ≤ B ∧
      eVariationOn (S.b u) (Icc u T) ≤ B)
    (hvi : ∀ v ∈ Icc 0 T, eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ B ∧
      eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ B ∧
      eVariationOn (fun u => S.a u v) (Icc 0 v) ≤ B ∧
      eVariationOn (fun u => S.b u v) (Icc 0 v) ≤ B)
    (haxis : ∀ t, (t, t) ∈ triangle 0 T → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      (∀ u a b, outSeg u a b ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (S.phi u) (Icc a b) ≤ ENNReal.ofReal η) ∧
      (∀ a b v, inSeg a b v ⊆ triangle 0 T ∩ triangle (t - δ) (t + δ) →
        eVariationOn (fun u => S.phi u v) (Icc a b) ≤ ENNReal.ofReal η)) :
    IsSolution e S (triangle 0 T) := by
  obtain ⟨hout, hin⟩ := hlim.integral_equations_of_c1 hT hc1 hr hl hn hg
  have cMu := hMu.continuousOn (Eventually.of_forall fun n => (hc1 n).continuousOn_mu hT).frequently
  refine {
    subset := fun _ hp => hp.2.1
    r_pos := hr
    lam_pos := hl
    nu_neg := hn
    one_sub_mu_pos := hg
    cont_r := hlim.unif_r.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_r.continuousOn).frequently
    cont_lam := hlim.unif_lam.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_lam.continuousOn).frequently
    cont_nu := hlim.unif_nu.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_nu.continuousOn).frequently
    cont_m := hlim.unif_m.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_m.continuousOn).frequently
    cont_Q := hlim.unif_Q.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_Q.continuousOn).frequently
    cont_phi := hlim.unif_phi.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_phi.continuousOn).frequently
    cont_A := hlim.unif_A.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_A.continuousOn).frequently
    cont_theta := hlim.unif_theta.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_theta.continuousOn).frequently
    cont_xi := hlim.unif_xi.continuousOn (Eventually.of_forall fun n => (hc1
        n).c1_xi.continuousOn).frequently
    eq_out := hout
    eq_in := hin
    ac_out := fun _ _ _ hab hs => ⟨out_ac_mono hro hab hs, out_ac_mono hmo hab hs,
      out_ac_mono hQo hab hs, out_ac_mono hpo hab hs, out_ac_mono hao hab hs⟩
    ac_in := fun _ _ _ hab hs => ⟨in_ac_mono hri hab hs, in_ac_mono hmi hab hs,
      in_ac_mono hQi hab hs, in_ac_mono hpi hab hs⟩
    bv_loc := ?_
    axis_small_var := haxis
    axis := ?_
    axis_mu := ?_ }
  · intro K hK _
    refine ⟨B, lt_top_iff_ne_top.mpr hB, ?_, ?_⟩
    · intro u a b hs
      have hh := hs.trans hK
      exact ⟨out_var_le (fun u hu => (hvo u hu).1) hh,
        out_var_le (fun u hu => (hvo u hu).2.1) hh,
        out_var_le (fun u hu => (hvo u hu).2.2.1) hh,
        out_var_le (fun u hu => (hvo u hu).2.2.2) hh⟩
    · intro a b v hs
      have hh := hs.trans hK
      exact ⟨in_var_le (fun v hv => (hvi v hv).1) hh,
        in_var_le (fun v hv => (hvi v hv).2.1) hh,
        in_var_le (fun v hv => (hvi v hv).2.2.1) hh,
        in_var_le (fun v hv => (hvi v hv).2.2.2) hh⟩
  · intro t ht
    have ht' : t ∈ Icc 0 T := ⟨ht.1, ht.2.2⟩
    have hm : S.m t t = 0 := tendsto_nhds_unique (hlim.unif_m.tendsto_at ht)
      (by simpa only [Function.uncurry_apply_pair, fun n => ((hc1 n).axis t ht).2.1] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    have hQ : S.Q t t = 0 := tendsto_nhds_unique (hlim.unif_Q.tendsto_at ht)
      (by simpa only [Function.uncurry_apply_pair, fun n => ((hc1 n).axis t ht).2.2.1] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    have hln : S.lam t t + S.nu t t = 0 :=
      tendsto_nhds_unique ((hlim.unif_lam.tendsto_at ht).add (hlim.unif_nu.tendsto_at ht))
        (by simpa only [Function.uncurry_apply_pair, fun n => ((hc1 n).axis t ht).2.2.2.1] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    exact ⟨hlim.axis_radius_of_c1 hc1 t ht', hm, hQ, hln,
      hlim.axis_scalar_matching_of_c1 hc1 t ht'⟩
  · intro t ht
    have hh := (cMu (t, t) ht).mono (s := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) inter_subset_left
    change Tendsto (Function.uncurry S.mu)
      (𝓝[triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)) (𝓝 (S.mu t t)) at hh
    simpa only [Function.uncurry_apply_pair, Fields.mu,
      hlim.axis_radius_of_c1 hc1 t ⟨ht.1, ht.2.2⟩, div_zero] using hh

end EmcsfAcExtension.Local
