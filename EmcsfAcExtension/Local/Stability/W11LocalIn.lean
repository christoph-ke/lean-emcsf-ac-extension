module

public import EmcsfAcExtension.Local.Stability.AssemblyIdentity
import EmcsfAcExtension.Local.Stability.MomentsReflection
public import EmcsfAcExtension.Local.Stability.MomentsODE

/-! # Incoming Hardy on shortened classical sections

The incoming section is parametrized by `t = -u`. Its radius derivative
is `-ν`, its forcing is `-k/(1-μ)`, and its real connection is `-e A`.
These are conditional analytic helpers; they close no graph node on their own.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- Incoming moment assuming the exact incoming reconstruction identity on
closed sections. The coefficient is exactly `4`, uniformly in all parameters
and every `0 < p ≤ 1 - ε²`. The integral has increasing original-coordinate
limits `u ≤ s ≤ v`; no phase magnitude or sign is discarded. -/
private theorem in_short_radial_bounds_aux (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.xi s v / (S.nu s v : ℂ))
        (kC1 e (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.nu u v / S.r u v * (1 - ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2)) •
            (S.xi u v / (S.nu u v : ℂ)) -
          (e * S.A u v) • (Complex.I * (S.xi u v / (S.nu u v : ℂ)))) (Icc 0 v) u)
    {p u v : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S.xi u v / (S.nu u v : ℂ)‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S.r s v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) s ∧
    (∫⁻ s in Icc u v, ENNReal.ofReal
      (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖)) ≤
      ENNReal.ofReal (4 * p⁻¹) * ∫⁻ s in Icc u v, inEnv T (kC1 e (triangle 0 T) S) s := by
  have hmap : MapsTo (fun t => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have hw : ContinuousOn (fun t => -S.nu (-t) v) (uIcc (-v) (-u)) := by
    rw [uIcc_of_le (neg_le_neg huv.le)]
    exact (hset.c1.c1_nu.continuousOn.comp
      (continuous_neg.prodMk continuous_const).continuousOn hmap).neg
  have hf : AbsolutelyContinuousOnInterval
      (fun t => S.xi (-t) v / (S.nu (-t) v : ℂ)) (-v) (-u) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le (neg_le_neg huv.le)]
    exact (stab_in_ratio_c1 hset.c1).comp
      (contDiffOn_id.neg.prodMk contDiffOn_const) hmap
  have hfa : S.xi (-(-v)) v / (S.nu (-(-v)) v : ℂ) = 0 := by
    simpa only [neg_neg] using stab_in_ratio_axis hset ⟨hu.trans huv.le, hvT⟩
  have hrad (t : ℝ) (ht : t ∈ Icc (-v) (-u)) :
      (∫ s in -v..t, -S.nu (-s) v) = S.r (-t) v :=
    stab_radius_reflected_integral hset hu huv.le hvT ht
  have hrb : 0 < ∫ s in -v..-u, -S.nu (-s) v := by
    rw [hrad (-u) ⟨neg_le_neg huv.le, le_rfl⟩, neg_neg]
    exact hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hqcc := stab_aestronglyMeasurable_neg_Icc
    (stab_in_forcing_measurable hset hu huv.le hvT)
  have hq : AEStronglyMeasurable
      (fun t => ‖-(kC1 e (triangle 0 T) S (-t) v / ((1 - S.mu (-t) v : ℝ) : ℂ))‖)
      (volume.restrict (Ioc (-v) (-u))) := by
    simpa only [norm_neg] using! hqcc.mono_measure
      (Measure.restrict_mono (show Ioc (-v) (-u) ⊆ Icc (-v) (-u) from
        fun _ ht => ⟨ht.1.le, ht.2⟩) le_rfl)
  have hd : ∀ t ∈ Ioo (-v) (-u),
      p * (-S.nu (-t) v / ∫ s in -v..t, -S.nu (-s) v) ≤
        -S.nu (-t) v / S.r (-t) v * (1 - ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ^ 2) := by
    intro t ht
    rw [hrad t ⟨ht.1.le, ht.2.le⟩]
    have hpt := hmap ⟨ht.1.le, ht.2.le⟩
    have hbox := hset.box.2 (-t, v) hpt
    have hy : ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ≤ ε :=
      (le_add_of_nonneg_left (norm_nonneg (S.theta (-t) v / (S.lam (-t) v : ℂ)))).trans
        hbox.2.2.2.2.2.1
    have hsq := mul_self_le_mul_self (norm_nonneg _) hy
    have hp' : p ≤ 1 - ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ^ 2 := by
      nlinarith only [hp, hsq]
    have hrpos := hset.c1.r_pos (-t, v) hpt (by linarith only [ht.1])
    have hw0 := (hset.c1.nu_neg (-t, v) hpt).le
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp'
      (div_nonneg (neg_nonneg.mpr hw0) hrpos.le)
  have hid : ∀ t ∈ Ioo (-v) (-u),
      HasDerivWithinAt (fun t => S.xi (-t) v / (S.nu (-t) v : ℂ))
        (-(kC1 e (triangle 0 T) S (-t) v / ((1 - S.mu (-t) v : ℝ) : ℂ)) -
          (-S.nu (-t) v / S.r (-t) v *
            (1 - ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖ ^ 2)) •
              (S.xi (-t) v / (S.nu (-t) v : ℂ)) -
          (-(e * S.A (-t) v)) • (Complex.I * (S.xi (-t) v / (S.nu (-t) v : ℂ))))
        (Icc (-v) (-u)) t := by
    intro t ht
    have hut : 0 < -t := by linarith only [hu, ht.2]
    have htv : -t < v := by linarith only [ht.1]
    have h := (hidentity (-t) v hut.le htv hvT).hasDerivAt (Icc_mem_nhds hut htv)
    have h' := (by simpa only [zero_sub] using! h :
      HasDerivAt (fun s => S.xi s v / (S.nu s v : ℂ)) _ (0 - t)).comp_const_sub 0 t
    simpa only [zero_sub, add_zero, neg_div, neg_mul, neg_smul, sub_eq_add_neg,
      neg_add_rev, neg_neg, add_assoc, add_comm, add_left_comm] using!
        h'.hasDerivWithinAt (s := Icc (-v) (-u))
  have hi := stab_radial_moment_of_identity (neg_le_neg huv.le) hp0 hw.intervalIntegrable
    (fun t ht => (neg_pos.mpr (hset.c1.nu_neg (-t, v) (hmap ht))).le)
    hf hfa hrb hq hd hid
  have hh := stab_radial_hardy_of_identity (neg_le_neg huv.le) hp0 hw.intervalIntegrable
    (fun t ht => (neg_pos.mpr (hset.c1.nu_neg (-t, v) (hmap ht))).le) hf hfa hq hd hid
  constructor
  · simp only [neg_neg] at hi
    rw [restrict_Ioc_eq_restrict_Icc] at hi
    have heq : (∫⁻ t in Icc (-v) (-u),
        ENNReal.ofReal ((S.r (-t) v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) (-t)) =
        ∫⁻ s in Icc u v, ENNReal.ofReal ((S.r s v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) s := by
      simpa only using! stab_lintegral_neg_Icc
        (fun s => ENNReal.ofReal ((S.r s v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) s) u v
    rw [← heq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply hi.trans
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hrad t ht, hrad (-u) ⟨neg_le_neg huv.le, le_rfl⟩, neg_neg, norm_neg]
    have hpt := hmap ht
    have hrnonneg : 0 ≤ S.r (-t) v :=
      (div_nonneg (by linarith only [ht.1] : 0 ≤ v - -t) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (stab_radius_bounds hset hpt.1 hpt.2.1 hvT).1
    have hpow := Real.rpow_nonneg
      (div_nonneg hrnonneg (hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).le) p
    rw [ENNReal.ofReal_mul hpow]
    have hforce := ENNReal.ofReal_le_ofReal
      (stab_forcing_norm_le hset hpt.1 hpt.2.1 hvT (kC1 e (triangle 0 T) S (-t) v))
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hforce
    have hk : ENNReal.ofReal ‖kC1 e (triangle 0 T) S (-t) v‖ ≤
        inEnv T (kC1 e (triangle 0 T) S) (-t) := by
      rw [ofReal_norm]
      exact le_iSup_of_le v (le_iSup_of_le ⟨hpt.2.1, hvT⟩ le_rfl)
    calc
      _ ≤ ENNReal.ofReal ((S.r (-t) v / S.r u v) ^ p) *
          (ENNReal.ofReal 4 * inEnv T (kC1 e (triangle 0 T) S) (-t)) :=
        mul_le_mul' le_rfl (hforce.trans (mul_le_mul' le_rfl hk))
      _ = _ := by ac_rfl
  · rw [restrict_Ioc_eq_restrict_Icc] at hh
    have hleft : (∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
        (-S.nu (-t) v / (∫ s in -v..t, -S.nu (-s) v) *
          ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖)) =
        ∫⁻ s in Icc u v, ENNReal.ofReal
          (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖) := by
      calc
        _ = ∫⁻ t in Icc (-v) (-u), ENNReal.ofReal
            (-S.nu (-t) v / S.r (-t) v * ‖S.xi (-t) v / (S.nu (-t) v : ℂ)‖) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro t ht
          dsimp only
          rw [hrad t ht]
        _ = _ := by
          simpa only using! stab_lintegral_neg_Icc
            (fun s => ENNReal.ofReal
              (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖)) u v
    rw [hleft] at hh
    apply hh.trans
    have hforce : (∫⁻ t in Icc (-v) (-u),
        ENNReal.ofReal ‖-(kC1 e (triangle 0 T) S (-t) v /
          ((1 - S.mu (-t) v : ℝ) : ℂ))‖) ≤
        ENNReal.ofReal 4 * ∫⁻ s in Icc u v, inEnv T (kC1 e (triangle 0 T) S) s := by
      calc
        _ ≤ ∫⁻ t in Icc (-v) (-u),
            ENNReal.ofReal 4 * inEnv T (kC1 e (triangle 0 T) S) (-t) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          have hpt := hmap ht
          have hb := ENNReal.ofReal_le_ofReal (stab_forcing_norm_le hset
            hpt.1 hpt.2.1 hvT (kC1 e (triangle 0 T) S (-t) v))
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hb
          simp only [norm_neg]
          apply hb.trans
          apply mul_le_mul' le_rfl
          rw [ofReal_norm]
          exact le_iSup_of_le v (le_iSup_of_le ⟨hpt.2.1, hvT⟩ le_rfl)
        _ = ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
            inEnv T (kC1 e (triangle 0 T) S) s := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact stab_lintegral_neg_Icc _ u v
        _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set
          (show Icc u v ⊆ Icc u v from Subset.rfl))
    calc
      _ ≤ ENNReal.ofReal p⁻¹ *
          (ENNReal.ofReal 4 * ∫⁻ s in Icc u v, inEnv T (kC1 e (triangle 0 T) S) s) :=
        mul_le_mul' le_rfl hforce
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hp0.le), mul_comm p⁻¹]

/-- The linear incoming Hardy bound retains the actual shortened
axis-to-point interval in the original null coordinate. The coefficient
`16/3` is universal, independent of every parameter and derivative supremum. -/
theorem Stab.hardy_in_local_c1 (hset : StabSetting e T ε M A S h)
    (hε : ε ^ 2 ≤ 1 / 4) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc u v, ENNReal.ofReal
      (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖)) ≤
      ENNReal.ofReal (16 / 3) * ∫⁻ s in Icc u v,
        inEnv T (kC1 e (triangle 0 T) S) s := by
  rcases huv.eq_or_lt with rfl | huv
  · simp
  · have hb := (in_short_radial_bounds_aux hset
      (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT)
      (p := 3 / 4) (by norm_num) (by linarith only [hε]) hu huv hvT).2
    norm_num at hb ⊢
    exact hb

end EmcsfAcExtension.Local
