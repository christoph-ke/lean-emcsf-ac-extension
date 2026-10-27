module

public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Frozen.KIn
public import EmcsfAcExtension.Frozen.JOut
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Limit.Tags2IncomingHardy
import EmcsfAcExtension.Local.Limit.AcBridgeAdmissibility
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Local.Broad.Setup
import EmcsfAcExtension.Local.Broad.ScalarAverage

/-! # Incoming potential differentiation triangle in the AC class

The incoming AC Hardy bound is integrated in the second label. The broad
export discharges incoming normalized AC by construction and uniqueness;
only the original common box and independent envelopes remain as premises.
charged_SF_new_version.tex:L5453–5491.
-/

public section

open Set Filter MeasureTheory Complex
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- [internal] Characteristic AC form of the incoming triangle estimate.
The coefficient `2*Cb/c²` depends only on the fixed geometric box. All length,
coupling, background and initial derivative size dependence is explicit. -/
theorem potential_incoming_triangle_bound_of_ac {e T c Cb η M : ℝ} {S : Fields} {K : ℝ → ℝ}
    (hc : 0 < c) (hCb : 0 < Cb) (hη : 0 ≤ η) (hsmall : η ^ 2 ≤ 1 / 2)
    (hS : IsSolution e S (triangle 0 T)) (hbox : StabBox S c Cb η M (triangle 0 T))
    (hb : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v)
    (hK : IntervalIntegrable K volume 0 T)
    (hdom : ∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ p in triangle 0 v, ENNReal.ofReal
      (‖S.xi p.1 p.2 / S.nu p.1 p.2‖ / (p.2 - p.1))) ≤
        ENNReal.ofReal ((2 * Cb / c ^ 2) * T * ∫ u in (0 : ℝ)..T, K u) := by
  classical
  let Y := (triangle 0 v).indicator (fun p : ℝ × ℝ => S.xi p.1 p.2 / S.nu p.1 p.2)
  let F := fun p : ℝ × ℝ => ENNReal.ofReal (‖Y p‖ / (p.2 - p.1))
  have hsub : triangle 0 v ⊆ triangle 0 T := fun p hp => ⟨hp.1,hp.2.1,hp.2.2.trans hv.2⟩
  have hY : Measurable Y := by
    dsimp only [Y]
    rw [← Set.piecewise_eq_indicator]
    exact ((IsSolution.cont_incoming_ratio hS).mono hsub).measurable_piecewise
      continuousOn_const (measurableSet_triangle 0 v)
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp (hY.norm.div (measurable_snd.sub measurable_fst))
  have hK0 : 0 ≤ᵐ[volume.restrict (Icc 0 T)] K := by
    filter_upwards [hdom T ⟨hv.1.trans hv.2, le_rfl⟩] with u hu
    exact (norm_nonneg _).trans hu
  have hmass0 : 0 ≤ ∫ u in (0 : ℝ)..T, K u :=
    intervalIntegral.integral_nonneg_of_ae_restrict (hv.1.trans hv.2) hK0
  have hsection : ∀ w ∈ Icc 0 v,
      (∫⁻ u in Icc 0 w, F (u,w)) ≤
        ENNReal.ofReal ((2 * Cb / c ^ 2) * ∫ u in (0 : ℝ)..T, K u) := by
    intro w hw
    have hwT : w ∈ Icc 0 T := ⟨hw.1, hw.2.trans hv.2⟩
    let H u := -S.nu u w / S.r u w * ‖S.xi u w / S.nu u w‖
    have hiK : IntervalIntegrable K volume 0 w := hK.mono_set (by
      rw [uIcc_of_le hw.1, uIcc_of_le (hv.1.trans hv.2)]
      exact Icc_subset_Icc_right hwT.2)
    obtain ⟨hiH,hH⟩ := incoming_hardy_le_envelope_of_ac hc hη hsmall hS hbox hwT
      (hb w hwT) hiK (hdom w hwT)
    have hH0 : ∀ u ∈ Icc 0 w, 0 ≤ H u := by
      intro u hu
      have hp : (u,w) ∈ triangle 0 T := ⟨hu.1,hu.2,hwT.2⟩
      have hr0 : 0 ≤ S.r u w := by
        rcases hu.2.eq_or_lt with heq | huw
        · rw [heq, (hS.axis w ⟨hw.1,le_rfl,hwT.2⟩).1]
        · exact (hS.r_pos _ hp huw).le
      exact mul_nonneg (div_nonneg (neg_nonneg.mpr (hS.nu_neg _ hp).le) hr0) (norm_nonneg _)
    have hweight : ∀ u ∈ Icc 0 w, F (u,w) ≤ ENNReal.ofReal (Cb / c) * ENNReal.ofReal (H u) := by
      intro u hu
      have hpv : (u,w) ∈ triangle 0 v := ⟨hu.1,hu.2,hw.2⟩
      have hp := hsub hpv
      dsimp only [F,Y]
      rw [indicator_of_mem hpv, ← ENNReal.ofReal_mul (div_nonneg hCb.le hc.le)]
      apply ENNReal.ofReal_le_ofReal
      rcases hu.2.eq_or_lt with heq | huw
      · rw [heq, sub_self, div_zero]
        exact mul_nonneg (div_nonneg hCb.le hc.le) (hH0 w ⟨hw.1,le_rfl⟩)
      have hr := hS.r_pos _ hp huw
      have hrad := Broad.outgoing_radius_upper hS hu.2 (by
        rintro ⟨x,y⟩ ⟨rfl,hy⟩
        exact ⟨hu.1,hy.1,hy.2.trans hwT.2⟩)
        (fun y hy => (hbox.2 (u,y) ⟨hu.1,hy.1,hy.2.trans hwT.2⟩).2.1)
      have hn := (hbox.2 (u,w) hp).2.2.1
      have hrec : 1 / (w-u) ≤ (Cb / c) * (-S.nu u w / S.r u w) := by
        rw [← mul_div_assoc, div_le_div_iff₀ (sub_pos.mpr huw) hr]
        have hn' : 1 ≤ -S.nu u w / c := (le_div_iff₀ hc).2 (by simpa using hn)
        have hm := mul_le_mul_of_nonneg_left hn' (mul_nonneg hCb.le (sub_nonneg.mpr hu.2))
        calc
          1 * S.r u w ≤ Cb * (w-u) := by simpa only [one_mul] using hrad
          _ ≤ Cb * (w-u) * (-S.nu u w / c) := by simpa only [mul_one] using hm
          _ = _ := by ring
      have hm := mul_le_mul_of_nonneg_right hrec (norm_nonneg (S.xi u w / S.nu u w))
      simpa only [H, one_div_mul_eq_div, mul_assoc] using hm
    have hmass := intervalIntegral.integral_mono_interval le_rfl hw.1 hwT.2
      (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hK0) hK
    calc
      _ ≤ ∫⁻ u in Icc 0 w, ENNReal.ofReal (Cb/c) * ENNReal.ofReal (H u) :=
        setLIntegral_mono' measurableSet_Icc hweight
      _ = ENNReal.ofReal (Cb/c) * ENNReal.ofReal (∫ u in (0 : ℝ)..w, H u) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hw.1).1 hiH)
            (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu; exact hH0 u hu),
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hw.1]
      _ ≤ ENNReal.ofReal (Cb/c) * ENNReal.ofReal ((2/c) * ∫ u in (0 : ℝ)..T, K u) := by
        gcongr
        exact hH.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ Cb/c)]
        congr 1
        ring
  calc
    _ = ∫⁻ p in triangle 0 v, F p := by
      apply setLIntegral_congr_fun (measurableSet_triangle 0 v)
      intro p hp
      dsimp only [F,Y]
      rw [indicator_of_mem hp]
    _ = ∫⁻ w in Icc 0 v, ∫⁻ u in Icc 0 w, F (u,w) := by
      rw [Measure.volume_eq_prod]
      exact lintegral_triangle_eq_lintegral_lintegral_symm hF
    _ ≤ ∫⁻ w in Icc 0 v, ENNReal.ofReal ((2*Cb/c^2) * ∫ u in (0 : ℝ)..T, K u) :=
      setLIntegral_mono' measurableSet_Icc hsection
    _ = ENNReal.ofReal ((2*Cb/c^2) * v * ∫ u in (0 : ℝ)..T, K u) := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2*Cb/c^2) * ∫ u in (0 : ℝ)..T, K u)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; exact hv.2)

/-- [node restart-sec-bv-stability-independent#potential-incoming-triangle-bound]
The incoming triangle bound for broad normalized AC data and the original
independent envelopes. Incoming AC is discharged using the unconditional
construction and broad identification. The coefficient depends only on `c,Cb`;
the positive smallness threshold depends only on the fixed box and `H`,
before time, coupling,
background, datum, solution, envelope and section. `T=2R` is retained explicitly. -/
theorem potential_incoming_triangle_bound_ac (c Cb : ℝ)
    (hc : 0 < c) (hCb : 0 < Cb) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 < H → ∃ s : ℝ, 0 < s ∧
      ∀ (T e η M : ℝ) (h : ℝ → ℂ) (S : Fields) (J K : ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        IsSolution e S (triangle 0 T) → IsRestartData S h T →
        StabBox S c Cb η M (triangle 0 T) →
        IntervalIntegrable J volume 0 T → IntervalIntegrable K volume 0 T →
        (∀ᵐ v ∂volume.restrict (Icc 0 T), ‖jOut S 0 v‖ ≤ J v) →
        (∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u) →
        (∫ v in (0 : ℝ)..T, J v) ≤ H * η → η ^ 2 + sigma e M T ≤ s →
        ∀ v ∈ Icc 0 T, (∫⁻ p in triangle 0 v, ENNReal.ofReal
          (‖S.xi p.1 p.2 / S.nu p.1 p.2‖ / (p.2-p.1))) ≤
            ENNReal.ofReal (C * T * ∫ u in (0 : ℝ)..T, K u) := by
  refine ⟨2*Cb/c^2,by positivity,?_⟩
  intro H hH
  obtain ⟨s,C₀,hs,_,hid⟩ := ac_identification_of_envelope_inputs
    whole_triangle_existence stab_extended c H hc hH
  refine ⟨min s (1/2),lt_min hs (by norm_num),?_⟩
  intro T e η M h S J K hT hη hac hS hd hbox hJ hK hj hk hmass hsmall v hv
  have hb := (hid T e η M Cb h S J hT hη hac hS hd hbox hJ hj hmass
    (hsmall.trans (min_le_left _ _))).2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hηs : η^2 ≤ 1/2 := by linarith only [hsmall.trans (min_le_right _ _), hσ]
  exact potential_incoming_triangle_bound_of_ac hc hCb hη hηs hS hbox hb hK hk hv

end EmcsfAcExtension.Local
