module

public import EmcsfAcExtension.Local.Broad.GeometryIncomingFlux
public import EmcsfAcExtension.Local.Broad.GeometryMass
public import EmcsfAcExtension.Local.Broad.GeometryRay
public import EmcsfAcExtension.Local.Broad.GeometryInitial
import EmcsfAcExtension.Local.Api.EqOn

/-! # Broad geometric comparison by the two ordered optical integrations

The entering optical data agree by their actual constraints. The later
axis expansion is estimated through the incoming optical integration
before it enters the outgoing one (amendment internal project record).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-geometry]
Broad geometric comparison, charged_SF_new_version.tex:L5788–5827 and internal project record (GE).
For each fixed positive lower and finite upper geometric box `c,C`, the
positive constant precedes the triangle, coupling, scalar and variation
sizes and both solutions. The finite budget `L` need not be small. -/
theorem stab_broad_geometry (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields), s < t →
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      (∀ v ∈ Icc s t, S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      (geometry_distance s t S₁ S₂).toReal ≤
        K * L * (normalized_field_distance s t S₁ S₂).toReal +
        K * ε * L * (geometry_distance s t S₁ S₂).toReal +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) *
          ((normalized_field_distance s t S₁ S₂).toReal +
            ε * (geometry_distance s t S₁ S₂).toReal) := by
  obtain ⟨KI, hKI, hin⟩ := incoming_optical_flux_difference c C hc hC
  obtain ⟨KO, hKO, hout⟩ := outgoing_optical_flux_difference c C hc hC
  obtain ⟨KM, hKM, hmass⟩ := mass_sup_le_variation_error c C hc hC
  let B := C / c
  let KL := B * (KI + KM)
  let KQ := B * KM
  let KNL := B * (c⁻¹ * KL + KO) + B * KM
  let KNQ := B * c⁻¹ * KQ + B * KM
  let AL := KL + KNL + c⁻¹ * KL
  let AQ := KQ + KNQ + c⁻¹ * KQ
  let K := AL + AQ + 1
  have hB : 0 ≤ B := div_nonneg hC hc.le
  have hKL : 0 ≤ KL := by dsimp [KL]; positivity
  have hKQ : 0 ≤ KQ := by dsimp [KQ]; positivity
  have hKNL : 0 ≤ KNL := by dsimp [KNL]; positivity
  have hKNQ : 0 ≤ KNQ := by dsimp [KNQ]; positivity
  have hAL : 0 ≤ AL := by dsimp [AL]; positivity
  have hAQ : 0 ≤ AQ := by dsimp [AQ]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hst hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvo hvi haxis hdata hσ
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  let E := d + ε * g
  let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
  let X := KM * L * E + KM * σ * ε * E
  let BL := KL * L * E + KQ * σ * ε * E
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hBL : 0 ≤ BL := by dsimp [BL]; positivity
  have hboxM : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε := by
    intro S hS p hp
    rcases hbox S hS p hp with ⟨hl, hl', hn, hn', hm, hphi, ht, hx⟩
    exact ⟨hl, hl', hphi, ht⟩
  have hboxO : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε := by
    intro S hS p hp
    rcases hbox S hS p hp with ⟨hl, hl', hn, hn', hm, hphi, ht, hx⟩
    exact ⟨hl, hl', ht⟩
  have hboxI : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε := by
    intro S hS p hp
    rcases hbox S hS p hp with ⟨hl, hl', hn, hn', hm, hphi, ht, hx⟩
    exact ⟨hl, hl', hn, hn', hm, hphi, hx⟩
  have _hfin := geometry_distance_ne_top hS₁ hS₂ hc (fun p hp => (hbox S₁ (by simp) p hp).1)
  have hMu := hmass s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hboxM hosc hvo
  have hmu u v (hp : (u, v) ∈ triangle s t) : |S₁.mu u v - S₂.mu u v| ≤ X :=
    (abs_mu_sub_le_mass_ratio_distance hS₁ hS₂ hp).trans hMu
  have hgap u v (hp : (u, v) ∈ triangle s t) :
      |(1 - S₁.mu u v) - (1 - S₂.mu u v)| ≤ X := by
    rw [show (1 - S₁.mu u v) - (1 - S₂.mu u v) = -(S₁.mu u v - S₂.mu u v) by ring, abs_neg]
    exact hmu u v hp
  have hop S (hS : S ∈ ({S₁, S₂} : Set Fields)) (p : ℝ × ℝ) (hp : p ∈ triangle s t) :
      0 < S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ∧ S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ B ∧
      0 < -S.nu p.1 p.2 / (1 - S.mu p.1 p.2) ∧ -S.nu p.1 p.2 / (1 - S.mu p.1 p.2) ≤ B := by
    obtain ⟨hl, hl', hn, hn', hm, hphi, ht, hx⟩ := hbox S hS p hp
    exact ⟨div_pos (hc.trans_le hl) (hc.trans_le hm), div_le_div₀ hC hl' hc hm,
      div_pos (hc.trans_le hn) (hc.trans_le hm), div_le_div₀ hC hn' hc hm⟩
  have hs : outSeg s s t ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨le_rfl, hx.1, hx.2⟩
  have hinit := common_data_initial_constraint_agreement hS₁ hS₂ hst hs hs hdata
    (haxis S₁ (by simp) s ⟨le_rfl, hst.le⟩) (haxis S₂ (by simp) s ⟨le_rfl, hst.le⟩)
  have hlogK u v (hp : (u, v) ∈ triangle s t) :
      |Real.log (S₁.lam u v / (1 - S₁.mu u v)) -
        Real.log (S₂.lam u v / (1 - S₂.mu u v))| ≤ KI * L * E := by
    have hv : v ∈ Icc s t := ⟨hp.1.trans hp.2.1, hp.2.2⟩
    have hu : u ∈ Icc s v := ⟨hp.1, hp.2.1⟩
    have hseg : inSeg s v v ⊆ triangle s t := by
      rintro ⟨a, b⟩ ⟨ha, hb, rfl⟩
      exact ⟨ha, hb, hv.2⟩
    obtain ⟨ii, hi⟩ := hin s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hL hboxI hosc
      hvo hvi haxis hσ v hv u hu
    let f := fun x => Real.log (S₁.lam x v / (1 - S₁.mu x v)) -
      Real.log (S₂.lam x v / (1 - S₂.mu x v))
    have cf : ContinuousOn f (Icc s u) :=
      ((continuousOn_log_kappa_in hS₁ hseg).sub (continuousOn_log_kappa_in hS₂ hseg)).mono
        (fun x hx => ⟨hx.1, hx.2.trans hu.2⟩)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu.1 cf
      (f' := fun x => -((-S₁.nu x v) / S₁.r x v * ‖S₁.xi x v / S₁.nu x v‖ ^ 2 -
        (-S₂.nu x v) / S₂.r x v * ‖S₂.xi x v / S₂.nu x v‖ ^ 2))
      (fun x hx => by
        apply ((hasDerivAt_log_kappa_in hS₁ hseg ⟨hx.1, hx.2.trans_le hu.2⟩).sub
          (hasDerivAt_log_kappa_in hS₂ hseg ⟨hx.1, hx.2.trans_le hu.2⟩)).congr_deriv
        ring) ii.neg
    have hzero : f s = 0 := by
      have hpoint := hinit (s, v) ⟨rfl, hv⟩
      simp only [f, Fields.mu, hpoint.1, hpoint.2.1, hpoint.2.2.2.1, sub_self]
    rw [intervalIntegral.integral_neg, hzero, sub_zero] at heq
    change |f u| ≤ KI * L * E
    rw [← heq, abs_neg]
    exact hi
  have hLam u v (hp : (u, v) ∈ triangle s t) : |S₁.lam u v - S₂.lam u v| ≤ BL := by
    have ho₁ := hop S₁ (by simp) (u, v) hp
    have ho₂ := hop S₂ (by simp) (u, v) hp
    have hopt : |S₁.lam u v / (1 - S₁.mu u v) - S₂.lam u v / (1 - S₂.mu u v)| ≤ B * KI * L * E :=
      ((abs_sub_le_mul_abs_log_sub ho₁.1 ho₂.1 ho₁.2.1 ho₂.2.1).trans
        (mul_le_mul_of_nonneg_left (hlogK u v hp) hB)).trans_eq (by ring)
    have hbound := expansion_difference_of_optical_bounds
      (hS₁.one_sub_mu_pos (u, v) hp) (hS₂.one_sub_mu_pos (u, v) hp)
      (show 1 - S₂.mu u v ≤ 1 by linarith [(mu_mem_Ico hS₂ hp).1])
      (hS₁.lam_pos (u, v) hp).le hB (by positivity) ho₁.2.1 hopt (hgap u v hp)
    exact hbound.trans_eq (by dsimp [BL, X, KL, KQ]; ring)
  have hNu u v (hp : (u, v) ∈ triangle s t) :
      |S₁.nu u v - S₂.nu u v| ≤ KNL * L * E + KNQ * σ * ε * E := by
    have hu : u ∈ Icc s t := ⟨hp.1, hp.2.1.trans hp.2.2⟩
    have hseg : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    obtain ⟨ii, hi⟩ := hout s t e ε L S₁ S₂ hS₁ hS₂ hε hL hboxO hosc hvo u v hp
    let f := fun x => Real.log (-S₁.nu u x / (1 - S₁.mu u x)) -
      Real.log (-S₂.nu u x / (1 - S₂.mu u x))
    have cf : ContinuousOn f (Icc u v) :=
      (continuousOn_log_iota_out hS₁ hseg).sub (continuousOn_log_iota_out hS₂ hseg)
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp.2.1 cf
      (fun x hx => (hasDerivAt_log_iota_out hS₁ hseg hx).sub
        (hasDerivAt_log_iota_out hS₂ hseg hx)) ii
    have ax₁ := hS₁.axis u ⟨hu.1, le_rfl, hu.2⟩
    have ax₂ := hS₂.axis u ⟨hu.1, le_rfl, hu.2⟩
    have hn₁ : -S₁.nu u u = S₁.lam u u := by linarith [ax₁.2.2.2.1]
    have hn₂ : -S₂.nu u u = S₂.lam u u := by linarith [ax₂.2.2.2.1]
    have hfaxis : f u = Real.log (S₁.lam u u) - Real.log (S₂.lam u u) := by
      simp only [f, Fields.mu, ax₁.1, ax₂.1, div_zero, sub_zero, div_one, hn₁, hn₂]
    have haxislog : |f u| ≤ c⁻¹ * BL := by
      rw [hfaxis]
      exact (abs_log_sub_le_inv_mul_abs_sub hc
        (hbox S₁ (by simp) (u, u) ⟨hu.1, le_rfl, hu.2⟩).1
        (hbox S₂ (by simp) (u, u) ⟨hu.1, le_rfl, hu.2⟩).1).trans
        (mul_le_mul_of_nonneg_left (hLam u u ⟨hu.1, le_rfl, hu.2⟩) (inv_nonneg.mpr hc.le))
    have hlog : |f v| ≤ c⁻¹ * BL + KO * L * E := by
      have hf : f v = f u + ∫ x in u..v, S₁.lam u x / S₁.r u x * ‖S₁.theta u x / S₁.lam u x‖ ^ 2 -
          S₂.lam u x / S₂.r u x * ‖S₂.theta u x / S₂.lam u x‖ ^ 2 := by linarith only [heq]
      rw [hf]
      exact (abs_add_le _ _).trans (add_le_add haxislog hi)
    have ho₁ := hop S₁ (by simp) (u, v) hp
    have ho₂ := hop S₂ (by simp) (u, v) hp
    have hopt : |(-S₁.nu u v) / (1 - S₁.mu u v) - (-S₂.nu u v) / (1 - S₂.mu u v)| ≤
        B * (c⁻¹ * BL + KO * L * E) :=
      (abs_sub_le_mul_abs_log_sub ho₁.2.2.1 ho₂.2.2.1 ho₁.2.2.2 ho₂.2.2.2).trans
        (mul_le_mul_of_nonneg_left hlog hB)
    have hbound := expansion_difference_of_optical_bounds
      (hS₁.one_sub_mu_pos (u, v) hp) (hS₂.one_sub_mu_pos (u, v) hp)
      (show 1 - S₂.mu u v ≤ 1 by linarith [(mu_mem_Ico hS₂ hp).1])
      (neg_pos.mpr (hS₁.nu_neg (u, v) hp)).le hB (by positivity) ho₁.2.2.2 hopt (hgap u v hp)
    simpa only [neg_sub_neg, abs_sub_comm] using hbound.trans_eq
      (show B * (c⁻¹ * BL + KO * L * E) + B * X = KNL * L * E + KNQ * σ * ε * E by
        dsimp [BL, X, KNL, KNQ]; ring)
  have hRadius u v (hp : (u, v) ∈ triangle s t) :
      |S₁.r u v - S₂.r u v| / S₁.r u v ≤ c⁻¹ * BL := by
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
    · subst v
      simp only [(hS₁.axis u hp).1, div_zero]
      positivity
    · have hs : outSeg u u v ⊆ triangle s t := by
        rintro p ⟨rfl, hx⟩
        exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
      have cl₁ := continuousOn_out_section hS₁.cont_lam hs
      have cl₂ := continuousOn_out_section hS₂.cont_lam hs
      have heqr : S₁.r u v - S₂.r u v = ∫ x in u..v, S₁.lam u x - S₂.lam u x := by
        rw [← outgoing_radius_reconstruction hS₁ hp.2.1 hs,
          ← outgoing_radius_reconstruction hS₂ hp.2.1 hs,
          intervalIntegral.integral_sub
            (ContinuousOn.intervalIntegrable_of_Icc hp.2.1 cl₁)
            (ContinuousOn.intervalIntegrable_of_Icc hp.2.1 cl₂)]
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := u) (b := v) (f := fun x => S₁.lam u x - S₂.lam u x) (C := BL)
        (fun x hx => by
          have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le hp.2.1] using uIoc_subset_uIcc hx
          simpa only [Real.norm_eq_abs] using hLam u x (hs ⟨rfl, hx'⟩))
      rw [← heqr, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp.2.1)] at hInt
      have hlow := outgoing_radius_lower hS₁ hp.2.1 hs
        (fun x hx => (hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1)
      apply (div_le_iff₀ (hS₁.r_pos (u, v) hp huv)).mpr
      apply hInt.trans
      calc
        BL * (v - u) = (c⁻¹ * BL) * (c * (v - u)) := by field_simp
        _ ≤ (c⁻¹ * BL) * S₁.r u v := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hSup : geometry_distance s t S₁ S₂ ≤ ENNReal.ofReal (K * L * E + K * σ * ε * E) := by
    apply iSup₂_le
    rintro ⟨u, v⟩ hp
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ BL + (KNL * L * E + KNQ * σ * ε * E) + c⁻¹ * BL :=
        add_le_add (add_le_add (hLam u v hp) (hNu u v hp)) (hRadius u v hp)
      _ = AL * (L * E) + AQ * (σ * ε * E) := by dsimp [AL, AQ, BL]; ring
      _ ≤ K * (L * E) + K * (σ * ε * E) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [K]
          linarith
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          dsimp [K]
          linarith
      _ = _ := by ring
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSup
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ K * L * E + K * σ * ε * E)] at hReal
  calc
    g ≤ K * L * E + K * σ * ε * E := hReal
    _ ≤ K * L * E + K * σ * 1 * E := by gcongr
    _ = _ := by dsimp [E, d, g, σ]; ring

end EmcsfAcExtension.Local
