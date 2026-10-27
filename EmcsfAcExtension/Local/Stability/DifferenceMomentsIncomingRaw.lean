module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingComparison
public import EmcsfAcExtension.Local.Stability.DifferenceMomentsODE
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Exact unabsorbed incoming difference forcing

The reflected parameter increases from the axis. The first connection
cancels in the norm equation; the difference of the connections remains
in the forcing. This helper performs no mass or potential absorption.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The incoming difference has the `1/2` moment of its exact forcing,
with coefficient `1` uniformly in all parameters, the pair and minimum
radius. Both connection terms are retained in deriving this helper. -/
theorem stab_in_difference_moment_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : 3 * ε ^ 2 ≤ 1 / 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let q := fun s : ℝ =>
      kC1 e (triangle 0 T) S₁ s v / ((1 - S₁.mu s v : ℝ) : ℂ) -
      kC1 e (triangle 0 T) S₂ s v / ((1 - S₂.mu s v : ℝ) : ℂ) -
      (S₁.nu s v / S₁.r s v - S₂.nu s v / S₂.r s v) •
        (S₂.xi s v / (S₂.nu s v : ℂ) -
          ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2 • (S₂.xi s v / (S₂.nu s v : ℂ))) -
      (e * (S₁.A s v - S₂.A s v)) • (Complex.I * (S₂.xi s v / (S₂.nu s v : ℂ)))
    ENNReal.ofReal ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤
      ∫⁻ s in Icc u v, ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (1 / 2 : ℝ) * ‖q s‖) := by
  let y₁ := fun s : ℝ => S₁.xi s v / (S₁.nu s v : ℂ)
  let y₂ := fun s : ℝ => S₂.xi s v / (S₂.nu s v : ℂ)
  let a₁ := fun s : ℝ => S₁.nu s v / S₁.r s v
  let a₂ := fun s : ℝ => S₂.nu s v / S₂.r s v
  let q := fun s : ℝ =>
    kC1 e (triangle 0 T) S₁ s v / ((1 - S₁.mu s v : ℝ) : ℂ) -
    kC1 e (triangle 0 T) S₂ s v / ((1 - S₂.mu s v : ℝ) : ℂ) -
    (a₁ s - a₂ s) • (y₂ s - ‖y₂ s‖ ^ 2 • y₂ s) -
    (e * (S₁.A s v - S₂.A s v)) • (Complex.I * y₂ s)
  change ENNReal.ofReal ‖y₁ u - y₂ u‖ ≤
    ∫⁻ s in Icc u v, ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (1 / 2 : ℝ) * ‖q s‖)
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Ico u v) (triangle 0 T) :=
    fun s hs => ⟨hu.trans hs.1, hs.2.le, hvT⟩
  have cK₁ := (continuousOn_kC1_aux h₁s.pos h₁s.c1).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cK₂ := (continuousOn_kC1_aux h₂s.pos h₂s.c1).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cG₁ : ContinuousOn (fun s : ℝ => 1 - S₁.mu s v) (Ico u v) :=
    continuousOn_const.sub ((continuousOn_mu_aux h₁s.pos h₁s.c1).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap)
  have cG₂ : ContinuousOn (fun s : ℝ => 1 - S₂.mu s v) (Ico u v) :=
    continuousOn_const.sub ((continuousOn_mu_aux h₂s.pos h₂s.c1).comp
      (continuous_id.prodMk continuous_const).continuousOn hmap)
  have cA₁ : ContinuousOn a₁ (Ico u v) :=
    (h₁s.c1.c1_nu.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).div
      (h₁s.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap)
      (fun s hs => (h₁s.c1.r_pos (s, v) (hmap hs) hs.2).ne')
  have cA₂ : ContinuousOn a₂ (Ico u v) :=
    (h₂s.c1.c1_nu.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).div
      (h₂s.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap)
      (fun s hs => (h₂s.c1.r_pos (s, v) (hmap hs) hs.2).ne')
  have cY₂ : ContinuousOn y₂ (Ico u v) := (stab_in_ratio_c1 h₂s.c1).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cConn := (h₁s.c1.c1_A.continuousOn.sub h₂s.c1.c1_A.continuousOn).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cQ : ContinuousOn q (Ico u v) :=
    (((cK₁.div (Complex.continuous_ofReal.comp_continuousOn cG₁)
      (fun s hs => Complex.ofReal_ne_zero.mpr
        (h₁s.c1.one_sub_mu_pos (s, v) (hmap hs)).ne')).sub
      (cK₂.div (Complex.continuous_ofReal.comp_continuousOn cG₂)
        (fun s hs => Complex.ofReal_ne_zero.mpr
          (h₂s.c1.one_sub_mu_pos (s, v) (hmap hs)).ne'))).sub
      ((cA₁.sub cA₂).smul (cY₂.sub ((cY₂.norm.pow 2).smul cY₂)))).sub
      ((continuousOn_const.mul cConn).smul (continuousOn_const.mul cY₂))
  have hmapR : MapsTo (fun t : ℝ => (-t, v)) (Icc (-v) (-u)) (triangle 0 T) := by
    intro t ht
    exact ⟨by linarith only [hu, ht.2], by linarith only [ht.1], hvT⟩
  have cW : ContinuousOn (fun t => -S₁.nu (-t) v) (uIcc (-v) (-u)) := by
    rw [uIcc_of_le (neg_le_neg huv.le)]
    exact (h₁s.c1.c1_nu.continuousOn.comp
      (continuous_neg.prodMk continuous_const).continuousOn hmapR).neg
  have hAc₁ : AbsolutelyContinuousOnInterval (fun t => y₁ (-t)) (-v) (-u) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le (neg_le_neg huv.le)]
    exact (stab_in_ratio_c1 h₁s.c1).comp
      (contDiffOn_id.neg.prodMk contDiffOn_const) hmapR
  have hAc₂ : AbsolutelyContinuousOnInterval (fun t => y₂ (-t)) (-v) (-u) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le (neg_le_neg huv.le)]
    exact (stab_in_ratio_c1 h₂s.c1).comp
      (contDiffOn_id.neg.prodMk contDiffOn_const) hmapR
  have haxis : y₁ (-(-v)) = y₂ (-(-v)) := by
    rw [neg_neg, show y₁ v = 0 from stab_in_ratio_axis h₁s ⟨hu.trans huv.le, hvT⟩,
      show y₂ v = 0 from stab_in_ratio_axis h₂s ⟨hu.trans huv.le, hvT⟩]
  have cQR : ContinuousOn (fun t => -(q (-t))) (Ioc (-v) (-u)) :=
    (cQ.comp continuous_neg.continuousOn (by
      intro t ht
      exact ⟨by linarith only [ht.2], by linarith only [ht.1]⟩)).neg
  have hrad (t : ℝ) (ht : t ∈ Icc (-v) (-u)) :
      (∫ s in -v..t, -S₁.nu (-s) v) = S₁.r (-t) v :=
    stab_radius_reflected_integral h₁s hu huv.le hvT ht
  have hidentity : ∀ t ∈ Ioo (-v) (-u),
      HasDerivWithinAt (fun s => y₁ (-s) - y₂ (-s))
        (-(q (-t)) - (-S₁.nu (-t) v / ∫ s in -v..t, -S₁.nu (-s) v) •
          ((y₁ (-t) - ‖y₁ (-t)‖ ^ 2 • y₁ (-t)) -
            (y₂ (-t) - ‖y₂ (-t)‖ ^ 2 • y₂ (-t))) -
          (-(e * S₁.A (-t) v)) • (Complex.I * (y₁ (-t) - y₂ (-t)))) (Icc (-v) (-u)) t := by
    intro t ht
    have hut : 0 < -t := by linarith only [hu, ht.2]
    have htv : -t < v := by linarith only [ht.1]
    have h₁d := (stab_in_reconstruction_smul h₁s.c1 hut.le htv hvT).hasDerivAt
      (Icc_mem_nhds hut htv)
    have h₂d := (stab_in_reconstruction_smul h₂s.c1 hut.le htv hvT).hasDerivAt
      (Icc_mem_nhds hut htv)
    have hd := (by simpa only [zero_sub] using! h₁d.sub h₂d :
      HasDerivAt (fun s => y₁ s - y₂ s) _ (0 - t)).comp_const_sub 0 t
    have hdR := hd.hasDerivWithinAt (s := Icc (-v) (-u))
    simp only [zero_sub] at hdR
    apply hdR.congr_deriv
    rw [hrad t ⟨ht.1.le, ht.2.le⟩]
    dsimp only [q, a₁, a₂, y₁, y₂]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow, neg_div]
    ring
  have hi := stab_radial_difference_moment_of_identity
    (neg_le_neg huv.le) (by norm_num : (0 : ℝ) < 1 / 2) (by linarith only [hε])
    cW.intervalIntegrable
    (fun t ht => (neg_pos.mpr (h₁s.c1.nu_neg (-t, v) (hmapR ht))).le)
    hAc₁ hAc₂ haxis
    (fun t ht => (le_add_of_nonneg_left (norm_nonneg
      (S₁.theta (-t) v / (S₁.lam (-t) v : ℂ)))).trans
      (h₁s.box.2 (-t, v) (hmapR ⟨ht.1.le, ht.2.le⟩)).2.2.2.2.2.1)
    (fun t ht => (le_add_of_nonneg_left (norm_nonneg
      (S₂.theta (-t) v / (S₂.lam (-t) v : ℂ)))).trans
      (h₂s.box.2 (-t, v) (hmapR ⟨ht.1.le, ht.2.le⟩)).2.2.2.2.2.1)
    (by rw [hrad (-u) ⟨neg_le_neg huv.le, le_rfl⟩, neg_neg]
        exact h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv)
    (cQR.norm.aestronglyMeasurable measurableSet_Ioc) hidentity
  simp only [neg_neg] at hi
  rw [restrict_Ioc_eq_restrict_Icc] at hi
  apply hi.trans_eq
  rw [← stab_lintegral_neg_Icc (a := u) (b := v)]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [hrad t ht, hrad (-u) ⟨neg_le_neg huv.le, le_rfl⟩, neg_neg, norm_neg]

end EmcsfAcExtension.Local
