module

public import EmcsfAcExtension.Local.Limit.StabilityPointwise
public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Assembly.Bundles
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.TriangleCauchy
import EmcsfAcExtension.Infra.Mixed.SupSum

/-! # Passing the classical pair comparison to existing strong limits

internal project record L1/L2: Fatou retains the sum of both envelope masses and all
pointwise comparison terms. Variation semicontinuity retains the sum of
the two characteristic suprema. No new AC solution is constructed here.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem liminf_add_le {a b : ℕ → ℝ≥0∞} :
    liminf a atTop + liminf b atTop ≤ liminf (a + b) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat]
  apply ENNReal.iSup_add_iSup_le
  intro i j
  apply le_iSup_of_le (max i j)
  apply le_iInf₂
  intro k hk
  exact add_le_add (iInf₂_le_of_le k ((le_max_left i j).trans hk) le_rfl)
    (iInf₂_le_of_le k ((le_max_right i j).trans hk) le_rfl)

private noncomputable def pointCost (S₁ S₂ : Fields) (p₁ p₂ p₃ p₄ : ℝ × ℝ) : ℝ :=
  (|S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| + |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| +
    |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2) +
    ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ + ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
    ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖

private theorem norm_sub_four (a b c d : ℂ) :
    ‖a - b‖ₑ ≤ ‖c - d‖ₑ + ‖c - a‖ₑ + ‖d - b‖ₑ := by
  calc
    _ = edist a b := by rw [edist_eq_enorm_sub]
    _ ≤ edist a c + (edist c d + edist d b) :=
      (edist_triangle a c b).trans (add_le_add le_rfl (edist_triangle c d b))
    _ = _ := by rw [edist_comm a c]; simp only [edist_eq_enorm_sub]; ac_rfl

private theorem point_bound_of_bounds {C e T M d : ℝ} {S₁ S₂ : Fields}
    (hb : StabBounds C e T M d S₁ S₂) (p₁ p₂ p₃ p₄ : ℝ × ℝ)
    (hp₁ : p₁ ∈ triangle 0 T) (hp₂ : p₂ ∈ triangle 0 T)
    (hp₃ : p₃ ∈ triangle 0 T) (hp₄ : p₄ ∈ triangle 0 T)
    (hr : 0 ≤ S₁.r p₁.1 p₁.2) :
    jDist T S₁ S₂ + kDist e T S₁ S₂ + ENNReal.ofReal (pointCost S₁ S₂ p₁ p₂ p₃ p₄) ≤
      ENNReal.ofReal (C * d) := by
  let g := |S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| +
    |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| + |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2
  have hg0 : 0 ≤ g := by dsimp only [g]; positivity
  have hg : ENNReal.ofReal g ≤ geomDist T S₁ S₂ := le_iSup₂_of_le p₁ hp₁ le_rfl
  have ha : ENNReal.ofReal ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ ≤ supDist T S₁.a S₂.a := by
    rw [ofReal_norm, supDist_def]; exact le_iSup₂_of_le p₂ hp₂ le_rfl
  have hb' : ENNReal.ofReal ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ ≤ supDist T S₁.b S₂.b := by
    rw [ofReal_norm, supDist_def]; exact le_iSup₂_of_le p₃ hp₃ le_rfl
  have hp : ENNReal.ofReal ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ ≤ supDist T S₁.phi S₂.phi := by
    rw [ofReal_norm, supDist_def]; exact le_iSup₂_of_le p₄ hp₄ le_rfl
  have hh := add_le_add (add_le_add (add_le_add
    (add_le_add (le_refl (jDist T S₁ S₂ + kDist e T S₁ S₂)) hg) ha) hb') hp
  have he : ENNReal.ofReal (pointCost S₁ S₂ p₁ p₂ p₃ p₄) =
      ENNReal.ofReal g + ENNReal.ofReal ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ +
        ENNReal.ofReal ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
        ENNReal.ofReal ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ := by
    change ENNReal.ofReal (((g + _) + _) + _) = _
    rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _),
      ENNReal.ofReal_add (by positivity) (norm_nonneg _), ENNReal.ofReal_add hg0 (norm_nonneg _)]
  apply le_trans ?_ hb.main
  rw [he]
  simpa only [add_assoc] using hh

/-- Pass a supplied universal classical comparison bound to two existing
strong limits. The constant `C` is unchanged and retains the producer's
scope. The comparison settings, data-distance limit and smooth conclusion
are explicit helper premises, discharged by the final conditional export.
`Assembly.Bundles` is a statement-only leaf; no assembly theorem is imported. -/
theorem stab_conclusion_of_smooth_bounds {C e T q M A : ℝ}
    {Sn₁ Sn₂ : ℕ → Fields} {hn₁ hn₂ : ℕ → ℝ → ℂ}
    {h₁ h₂ : ℝ → ℂ} {S₁ S₂ : Fields} {Δn : ℕ → ℝ}
    (hC : 0 ≤ C) (hl₁ : StrongLimit e T Sn₁ S₁) (hl₂ : StrongLimit e T Sn₂ S₂)
    (hs₁ : ∀ n, StabSetting e T q M A (Sn₁ n) (hn₁ n))
    (hs₂ : ∀ n, StabSetting e T q M A (Sn₂ n) (hn₂ n))
    (hΔ : Tendsto Δn atTop (𝓝 (dataDist h₁ h₂ T)))
    (hb : ∀ n, StabBounds C e T M (Δn n) (Sn₁ n) (Sn₂ n)) :
    StabConclusion C e T h₁ h₂ S₁ S₂ := by
  classical
  have hT := (hs₁ 0).pos
  have hg₁ := hl₁.lower_geometry_of_settings hs₁
  have hg₂ := hl₂.lower_geometry_of_settings hs₂
  have hL1 (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : S₁.lam p.1 p.2 ≠ 0 :=
      by have := (hg₁ p hp).1; linarith
  have hL2 (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : S₂.lam p.1 p.2 ≠ 0 :=
      by have := (hg₂ p hp).1; linarith
  have hN1 (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : S₁.nu p.1 p.2 ≠ 0 :=
      by have := (hg₁ p hp).2.1; linarith
  have hN2 (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : S₂.nu p.1 p.2 ≠ 0 :=
      by have := (hg₂ p hp).2.1; linarith
  have ha p hp := (hl₁.tendsto_a_of_lam_ne_zero hp (hL1 p hp)).sub
    (hl₂.tendsto_a_of_lam_ne_zero hp (hL2 p hp))
  have hb' p hp := (hl₁.tendsto_b_of_nu_ne_zero hp (hN1 p hp)).sub
    (hl₂.tendsto_b_of_nu_ne_zero hp (hN2 p hp))
  have htv : (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
      (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
      ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
    have hh := Mixed.iSup_eVariationOn_add_le_of_tendsto
      (F := fun n (u : Icc (0 : ℝ) T) v => (Sn₁ n).a u v - (Sn₂ n).a u v)
      (G := fun n (v : Icc (0 : ℝ) T) u => (Sn₁ n).b u v - (Sn₂ n).b u v)
      (f := fun (u : Icc (0 : ℝ) T) v => S₁.a u v - S₂.a u v)
      (g := fun (v : Icc (0 : ℝ) T) u => S₁.b u v - S₂.b u v)
      (s := fun u => Icc (u : ℝ) T) (t := fun v => Icc 0 (v : ℝ))
      (fun u v hv => ha (u, v) ⟨u.property.1, hv.1, hv.2⟩)
      (fun v u hu => hb' (u, v) ⟨hu.1, hu.2, v.property.2⟩)
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hΔ.const_mul C))
      (Eventually.of_forall fun n =>
          by simpa only [iSup_subtype, Function.comp_def] using (hb n).tv)
    simpa only [iSup_subtype] using hh
  obtain ⟨Dj₁, hjm₁, hjt₁, hj₁⟩ := hl₁.env_j
  obtain ⟨Dj₂, hjm₂, hjt₂, hj₂⟩ := hl₂.env_j
  obtain ⟨Dk₁, hkm₁, hkt₁, hk₁⟩ := hl₁.env_k
  obtain ⟨Dk₂, hkm₂, hkt₂, hk₂⟩ := hl₂.env_k
  let J₀ n := (Icc (0 : ℝ) T).indicator
    (outEnv 0 (fun u v => jC1 (triangle 0 T) (Sn₁ n) u v - jC1 (triangle 0 T) (Sn₂ n) u v))
  let K₀ n := (Icc (0 : ℝ) T).indicator
    (inEnv T (fun u v => kC1 e (triangle 0 T) (Sn₁ n) u v - kC1 e (triangle 0 T) (Sn₂ n) u v))
  have hJ₀ n : Measurable (J₀ n) := measurable_indicator_normEnvelope
    (((hs₁ n).c1.continuousOn_jC1 hT).sub ((hs₂ n).c1.continuousOn_jC1 hT))
  have hK₀ n : Measurable (K₀ n) := Mixed.measurable_indicator_incoming_envelope hT.le
    (((hs₁ n).c1.continuousOn_kC1 hT).sub ((hs₂ n).c1.continuousOn_kC1 hT))
  let Jn n v := J₀ n v + Dj₁ n v + Dj₂ n v
  let Kn n u := K₀ n u + Dk₁ n u + Dk₂ n u
  have hJn n : Measurable (Jn n) := ((hJ₀ n).add (hjm₁ n)).add (hjm₂ n)
  have hKn n : Measurable (Kn n) := ((hK₀ n).add (hkm₁ n)).add (hkm₂ n)
  let J v := liminf (fun n => Jn n v) atTop
  let K u := liminf (fun n => Kn n u) atTop
  have hJ : Measurable J := Measurable.liminf hJn
  have hK : Measurable K := Measurable.liminf hKn
  have hjdom : ∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T),
      ‖jOut S₁ u v - jOut S₂ u v‖ₑ ≤ J v := by
    intro u hu
    filter_upwards [ae_all_iff.2 (fun n => hj₁ n u hu), ae_all_iff.2 (fun n => hj₂ n u hu),
      ae_restrict_mem measurableSet_Icc] with v hv₁ hv₂ hv
    apply le_liminf_of_le (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    have hmem : v ∈ Icc 0 T := ⟨hu.1.trans hv.1, hv.2⟩
    have hz : J₀ n v = outEnv 0 (fun u v => jC1 (triangle 0 T) (Sn₁ n) u v -
        jC1 (triangle 0 T) (Sn₂ n) u v) v := indicator_of_mem hmem _
    exact (norm_sub_four _ _ _ _).trans
      (add_le_add (add_le_add (by rw [hz]; exact le_iSup₂_of_le u ⟨hu.1, hv.1⟩ le_rfl)
        (hv₁ n)) (hv₂ n))
  have hkdom : ∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v),
      ‖kIn e S₁ u v - kIn e S₂ u v‖ₑ ≤ K u := by
    intro v hv
    filter_upwards [ae_all_iff.2 (fun n => hk₁ n v hv), ae_all_iff.2 (fun n => hk₂ n v hv),
      ae_restrict_mem measurableSet_Icc] with u hu₁ hu₂ hu
    apply le_liminf_of_le (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    have hmem : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans hv.2⟩
    have hz : K₀ n u = inEnv T (fun u v => kC1 e (triangle 0 T) (Sn₁ n) u v -
        kC1 e (triangle 0 T) (Sn₂ n) u v) u := indicator_of_mem hmem _
    exact (norm_sub_four _ _ _ _).trans
      (add_le_add (add_le_add (by rw [hz]; exact le_iSup₂_of_le v ⟨hu.2, hv.2⟩ le_rfl)
        (hu₁ n)) (hu₂ n))
  have hJi n : (∫⁻ v in Icc 0 T, Jn n v) = jDist T (Sn₁ n) (Sn₂ n) +
      (∫⁻ v in Icc 0 T, Dj₁ n v) + ∫⁻ v in Icc 0 T, Dj₂ n v := by
    have h₁ := lintegral_add_left (μ := volume.restrict (Icc 0 T)) (hJ₀ n) (Dj₁ n)
    have h₂ := lintegral_add_left (μ := volume.restrict (Icc 0 T)) ((hJ₀ n).add (hjm₁ n)) (Dj₂ n)
    simp only [Pi.add_apply] at h₁ h₂
    dsimp only [Jn]
    rw [h₂, h₁]
    simp only [J₀, jDist, lintegral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_self]
  have hKi n : (∫⁻ u in Icc 0 T, Kn n u) = kDist e T (Sn₁ n) (Sn₂ n) +
      (∫⁻ u in Icc 0 T, Dk₁ n u) + ∫⁻ u in Icc 0 T, Dk₂ n u := by
    have h₁ := lintegral_add_left (μ := volume.restrict (Icc 0 T)) (hK₀ n) (Dk₁ n)
    have h₂ := lintegral_add_left (μ := volume.restrict (Icc 0 T)) ((hK₀ n).add (hkm₁ n)) (Dk₂ n)
    simp only [Pi.add_apply] at h₁ h₂
    dsimp only [Kn]
    rw [h₂, h₁]
    simp only [K₀, kDist, lintegral_indicator measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc, inter_self]
  let E n := ((∫⁻ v in Icc 0 T, Dj₁ n v) + ∫⁻ v in Icc 0 T, Dj₂ n v) +
    ((∫⁻ u in Icc 0 T, Dk₁ n u) + ∫⁻ u in Icc 0 T, Dk₂ n u)
  have hEt : Tendsto E atTop (𝓝 0) :=
      by simpa only [E, zero_add] using (hjt₁.add hjt₂).add (hkt₁.add hkt₂)
  have hRHS : Tendsto (fun n => ENNReal.ofReal (C * Δn n) + E n) atTop
      (𝓝 (ENNReal.ofReal (C * dataDist h₁ h₂ T))) := by
    simpa only [Function.comp_def, add_zero] using
      (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hΔ.const_mul C)).add hEt
  have hfatJ : (∫⁻ v in Icc 0 T, J v) ≤ liminf (fun n => ∫⁻ v in Icc 0 T, Jn n v) atTop :=
    lintegral_liminf_le' (fun n => (hJn n).aemeasurable)
  have hfatK : (∫⁻ u in Icc 0 T, K u) ≤ liminf (fun n => ∫⁻ u in Icc 0 T, Kn n u) atTop :=
    lintegral_liminf_le' (fun n => (hKn n).aemeasurable)
  have htotal (p₁ : ℝ × ℝ) (hp₁ : p₁ ∈ triangle 0 T)
      (p₂ : ℝ × ℝ) (hp₂ : p₂ ∈ triangle 0 T) (p₃ : ℝ × ℝ) (hp₃ : p₃ ∈ triangle 0 T)
      (p₄ : ℝ × ℝ) (hp₄ : p₄ ∈ triangle 0 T) :
      (∫⁻ v in Icc 0 T, J v) + (∫⁻ u in Icc 0 T, K u) +
        ENNReal.ofReal (pointCost S₁ S₂ p₁ p₂ p₃ p₄) ≤
        ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
    have hrad : Tendsto (fun n => |(Sn₁ n).r p₁.1 p₁.2 - (Sn₂ n).r p₁.1 p₁.2| /
        (Sn₁ n).r p₁.1 p₁.2) atTop (𝓝 (|S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2)) := by
      rcases hp₁.2.1.eq_or_lt with heq | hlt
      · have hz n := ((hs₁ n).c1.axis p₁.1 ⟨hp₁.1, le_rfl, heq.trans_le hp₁.2.2⟩).1
        have hzl := hl₁.axis_radius_of_c1 (fun n => (hs₁ n).c1)
          p₁.1 ⟨hp₁.1, heq.trans_le hp₁.2.2⟩
        simpa only [← heq, hz, hzl, div_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      · exact ((hl₁.unif_r.tendsto_at hp₁).sub (hl₂.unif_r.tendsto_at hp₁)).abs.div
          (hl₁.unif_r.tendsto_at hp₁)
          ((div_pos (sub_pos.2 hlt) (by norm_num : (0 : ℝ) < 4)).trans_le (hg₁ p₁ hp₁).2.2).ne'
    have hpt : Tendsto (fun n => pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄) atTop
        (𝓝 (pointCost S₁ S₂ p₁ p₂ p₃ p₄)) := by
      have hgeo := ((hl₁.unif_lam.tendsto_at hp₁).sub (hl₂.unif_lam.tendsto_at hp₁)).abs.add
        ((hl₁.unif_nu.tendsto_at hp₁).sub (hl₂.unif_nu.tendsto_at hp₁)).abs
      exact (((hgeo.add hrad).add (ha p₂ hp₂).norm).add (hb' p₃ hp₃).norm).add
        ((hl₁.unif_phi.tendsto_at hp₄).sub (hl₂.unif_phi.tendsto_at hp₄)).norm
    have hbpoint n : jDist T (Sn₁ n) (Sn₂ n) + kDist e T (Sn₁ n) (Sn₂ n) +
        ENNReal.ofReal (pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄) ≤ ENNReal.ofReal (C * Δn n) := by
      apply point_bound_of_bounds (hb n) p₁ p₂ p₃ p₄ hp₁ hp₂ hp₃ hp₄
      rcases hp₁.2.1.eq_or_lt with heq | hlt
      · have hz := ((hs₁ n).c1.axis p₁.1 ⟨hp₁.1, le_rfl, heq.trans_le hp₁.2.2⟩).1
        simpa only [← heq, hz] using (le_refl (0 : ℝ))
      · exact ((hs₁ n).c1.r_pos p₁ hp₁ hlt).le
    have hmass n : (∫⁻ v in Icc 0 T, Jn n v) + (∫⁻ u in Icc 0 T, Kn n u) +
        ENNReal.ofReal (pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄) ≤
        ENNReal.ofReal (C * Δn n) + E n := by
      calc
        _ = (jDist T (Sn₁ n) (Sn₂ n) + kDist e T (Sn₁ n) (Sn₂ n) +
            ENNReal.ofReal (pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄)) + E n := by
              rw [hJi, hKi]; dsimp only [E]; ac_rfl
        _ ≤ _ := add_le_add (hbpoint n) (le_refl (E n))
    have hpE : Tendsto (fun n => ENNReal.ofReal (pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄))
        atTop (𝓝 (ENNReal.ofReal (pointCost S₁ S₂ p₁ p₂ p₃ p₄))) := by
      simpa only [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hpt
    have hlow := add_le_add (add_le_add hfatJ hfatK)
      (le_refl (ENNReal.ofReal (pointCost S₁ S₂ p₁ p₂ p₃ p₄)))
    rw [← hpE.liminf_eq] at hlow
    have hmid := hlow.trans ((add_le_add liminf_add_le (le_refl _)).trans liminf_add_le)
    rw [hpE.liminf_eq] at hmid
    apply hmid.trans
    change liminf (fun n => (∫⁻ v in Icc 0 T, Jn n v) + (∫⁻ u in Icc 0 T, Kn n u) +
      ENNReal.ofReal (pointCost (Sn₁ n) (Sn₂ n) p₁ p₂ p₃ p₄)) atTop ≤ _
    exact (liminf_le_liminf (Eventually.of_forall hmass)).trans_eq hRHS.liminf_eq
  have hp0 : (0, 0) ∈ triangle 0 T := ⟨le_rfl, le_rfl, hT.le⟩
  have hmass := le_self_add.trans (htotal (0, 0) hp0 (0, 0) hp0 (0, 0) hp0 (0, 0) hp0)
  have hJfin : (∫⁻ v in Icc 0 T, J v) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hmass)
  have hKfin : (∫⁻ u in Icc 0 T, K u) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_add_self.trans hmass)
  have hJtop := ae_lt_top hJ hJfin
  have hKtop := ae_lt_top hK hKfin
  refine ⟨⟨fun v => (J v).toReal, fun u => (K u).toReal,
    integrable_toReal_of_lintegral_ne_top hJ.aemeasurable hJfin,
    integrable_toReal_of_lintegral_ne_top hK.aemeasurable hKfin, ?_, ?_, ?_⟩, htv⟩
  · intro u hu
    filter_upwards [hjdom u hu,
      ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hu.1 le_rfl) hJtop] with v hv ht
    simpa only [toReal_enorm] using ENNReal.toReal_mono ht.ne hv
  · intro v hv
    filter_upwards [hkdom v hv,
      ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl hv.2) hKtop] with u hu ht
    simpa only [toReal_enorm] using ENNReal.toReal_mono ht.ne hu
  · intro p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
    have hr : 0 ≤ S₁.r p₁.1 p₁.2 :=
      (div_nonneg (sub_nonneg.2 hp₁.2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans (hg₁ p₁ hp₁).2.2
    have hp : 0 ≤ pointCost S₁ S₂ p₁ p₂ p₃ p₄ := by dsimp only [pointCost]; positivity
    have hd0 : 0 ≤ dataDist h₁ h₂ T := by
      unfold dataDist
      exact add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (htotal p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄)
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hJfin, hKfin⟩) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hJfin hKfin, ENNReal.toReal_ofReal hp,
      ENNReal.toReal_ofReal (mul_nonneg hC hd0)] at hh
    rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
      integral_toReal hJ.aemeasurable hJtop, integral_toReal hK.aemeasurable hKtop]
    simpa only [pointCost, dataDist, add_assoc] using hh

end EmcsfAcExtension.Local
