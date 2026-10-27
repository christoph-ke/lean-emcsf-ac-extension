module

public import EmcsfAcExtension.Global.Exterior.RadiiProfile

/-! # Adaptive majorants on an arbitrary outer interval

The dyadic construction may start strictly below the prescribed outer
radius. Retain the additional top piece before taking the moving supremum.
This supplies the arbitrary-`R₀` interface of internal project record.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

namespace Exterior

/-- [internal]
The source step profile, with its linear top piece above the first
selected radius. This is the extra piece needed for arbitrary `R₀`. -/
@[expose] noncomputable def extendedStepRadiusProfile (R : ℕ → ℝ) (σ₀ x : ℝ) : ℝ :=
  if R 0 < x then σ₀ * x else stepRadiusProfile R σ₀ x

/-- [internal]
The extended profile is positive and bounded by its top slope on every
positive radius. The seed is fixed before the radius is quantified. -/
theorem extendedStepRadiusProfile_bounds {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0)) (hσ : 0 < σ₀)
    {x : ℝ} (hx : 0 < x) :
    0 < extendedStepRadiusProfile R σ₀ x ∧ extendedStepRadiusProfile R σ₀ x ≤ σ₀ * x := by
  unfold extendedStepRadiusProfile
  split_ifs with htop
  · exact ⟨mul_pos hσ hx, le_rfl⟩
  · exact stepRadiusProfile_bounds hR ht hσ ⟨hx, le_of_not_gt htop⟩

/-- [internal]
The top piece preserves monotonicity at the first selected radius. -/
theorem extendedStepRadiusProfile_monotoneOn {R : ℕ → ℝ} {σ₀ R₀ : ℝ}
    (hR : StrictAnti R) (ht : Tendsto R atTop (𝓝 0)) (hσ : 0 < σ₀) :
    MonotoneOn (extendedStepRadiusProfile R σ₀) (Ioc 0 R₀) := by
  intro x hx y hy hxy
  unfold extendedStepRadiusProfile
  by_cases hytop : R 0 < y
  · rw [ite_eq_left hytop]
    split_ifs with hxtop
    · exact mul_le_mul_of_nonneg_left hxy hσ.le
    · exact ((stepRadiusProfile_bounds hR.antitone ht hσ
        ⟨hx.1, le_of_not_gt hxtop⟩).2).trans (mul_le_mul_of_nonneg_left hxy hσ.le)
  · have hxtop : ¬R 0 < x := not_lt.mpr (hxy.trans (le_of_not_gt hytop))
    rw [ite_eq_right hytop, ite_eq_right hxtop]
    exact stepRadiusProfile_monotoneOn hR ht hσ.le
      ⟨hx.1, le_of_not_gt hxtop⟩ ⟨hy.1, le_of_not_gt hytop⟩ hxy

/-- [internal]
The top extension leaves the small-radius profile limit unchanged. -/
theorem extendedStepRadiusProfile_tendsto_div {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0))
    (hpos : ∀ j, 0 < R j) (hσ : 0 < σ₀) :
    Tendsto (fun x => extendedStepRadiusProfile R σ₀ x / x) (𝓝[>] 0) (𝓝 0) := by
  apply (stepRadiusProfile_tendsto_div hR ht hpos hσ).congr'
  filter_upwards [Ioo_mem_nhdsGT (hpos 0)] with x hx
  simp only [extendedStepRadiusProfile, ite_eq_right (not_lt.mpr hx.2.le)]

end Exterior

namespace Terminal

/-- [internal]
Architecture §3's adaptive majorant interface, on every prescribed
positive outer radius. The extra top piece contributes a finite mass
weight integral. The slope `k` is freely prescribed; all witnesses may
depend on `M`, `R₀` and `k`. No normalization of `R₀` is used. -/
theorem adaptive_majorant (M : ℝ → ℝ) (R₀ k : ℝ) (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (_hcont : ContinuousOn M (Ioc 0 R₀))
    (hsmall : Tendsto (fun R => M R / R) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / R ^ 2)) < ⊤) :
    ∃ ell : ℝ → ℝ, MonotoneOn ell (Ioc 0 R₀) ∧
      LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀) ∧
      (∀ R ∈ Ioc 0 R₀, 0 < ell R ∧ ell R ≤ k * R) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0) ∧
      (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤ := by
  have hσ : 0 < k / 4 := div_pos hk.1 (by norm_num)
  obtain ⟨R, hRb, hhalve, ht, hI, hm⟩ := Exterior.dyadic_radius_choice hR hσ hsmall hint
  have hpos (j : ℕ) := (hRb j).1
  have hanti : StrictAnti R := strictAnti_nat_of_succ_lt (fun j =>
    (hhalve j).trans_lt (by have hp := hpos j; linarith))
  let p := Exterior.extendedStepRadiusProfile R (k / 4)
  let ell := Exterior.radiusMajorant p R₀ k
  have hp (x : ℝ) (hx : x ∈ Ioc 0 R₀) : 0 < p x ∧ p x ≤ k / 4 * x :=
    Exterior.extendedStepRadiusProfile_bounds hanti.antitone ht hσ hx.1
  have hb (x : ℝ) (hx : x ∈ Ioc 0 R₀) : p x ≤ k / 2 * x :=
    (hp x hx).2.trans (mul_le_mul_of_nonneg_right (by linarith [hk.1] : k / 4 ≤ k / 2) hx.1.le)
  have hdom (x : ℝ) (hx : x ∈ Ioc 0 R₀) : p x ≤ ell x :=
    Exterior.le_radiusMajorant hk.1.le hx hb
  have hell (x : ℝ) (hx : x ∈ Ioc 0 R₀) : 0 < ell x :=
    (hp x hx).1.trans_le (hdom x hx)
  have hdomstep (x : ℝ) (hx : x ∈ Ioc 0 (R 0)) :
      Exterior.stepRadiusProfile R (k / 4) x ≤ ell x := by
    have hd := hdom x ⟨hx.1, hx.2.trans (hRb 0).2⟩
    simpa only [p, Exterior.extendedStepRadiusProfile, ite_eq_right (not_lt.mpr hx.2)] using hd
  refine ⟨ell, Exterior.radiusMajorant_monotoneOn hk.1.le
    (Exterior.extendedStepRadiusProfile_monotoneOn hanti ht hσ) hb,
    Exterior.radiusMajorant_lipschitzOnWith hk.1.le
    (Exterior.extendedStepRadiusProfile_monotoneOn hanti ht hσ) hb, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hell x hx, (Exterior.radiusMajorant_le hk.1.le hx hb).trans
      (mul_le_mul_of_nonneg_right (by linarith [hk.1] : k / 2 ≤ k) hx.1.le)⟩
  · exact Exterior.radiusMajorant_tendsto_div hR hk.1.le (fun x hx => (hp x hx).1.le) hb
      (Exterior.extendedStepRadiusProfile_tendsto_div hanti.antitone ht hpos hσ)
  · apply squeeze_zero' _ _ (Exterior.mass_div_stepRadiusProfile_tendsto hanti.antitone ht hpos hσ
      (fun x hx => hM x ⟨hx.1, hx.2.trans (hRb 0).2⟩) hm)
    · filter_upwards [Ioo_mem_nhdsGT hR] with x hx
      exact div_nonneg (hM x ⟨hx.1, hx.2.le⟩) (hell x ⟨hx.1, hx.2.le⟩).le
    · filter_upwards [Ioo_mem_nhdsGT (hpos 0)] with x hx
      exact div_le_div_of_nonneg_left (hM x ⟨hx.1, hx.2.le.trans (hRb 0).2⟩)
        (Exterior.stepRadiusProfile_bounds hanti.antitone ht hσ ⟨hx.1, hx.2.le⟩).1
        (hdomstep x ⟨hx.1, hx.2.le⟩)
  · have hinner := Exterior.adaptive_weight_integrable_of_dyadic hanti.antitone ht hpos hσ
      (fun x hx => hM x ⟨hx.1, hx.2.trans (hRb 0).2⟩) hdomstep hI
    have htop : (∫⁻ x in Ioc (R 0) R₀, ENNReal.ofReal (M x / ell x ^ 2)) < ⊤ := by
      have hle : (∫⁻ x in Ioc (R 0) R₀, ENNReal.ofReal (M x / ell x ^ 2)) ≤
          ENNReal.ofReal ((k / 4)⁻¹ ^ 2) *
            ∫⁻ x in Ioc 0 R₀, ENNReal.ofReal (M x / x ^ 2) := by
        calc
          _ ≤ ∫⁻ x in Ioc (R 0) R₀,
              ENNReal.ofReal ((k / 4)⁻¹ ^ 2) * ENNReal.ofReal (M x / x ^ 2) := by
            apply setLIntegral_mono' measurableSet_Ioc
            intro x hx
            have hx' : x ∈ Ioc 0 R₀ := ⟨(hpos 0).trans hx.1, hx.2⟩
            have hd := hdom x hx'
            have hd' : k / 4 * x ≤ ell x := by
              simpa only [p, Exterior.extendedStepRadiusProfile, ite_eq_left hx.1] using hd
            have hp' : 0 < k / 4 * x := mul_pos hσ hx'.1
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            calc
              _ ≤ M x / (k / 4 * x) ^ 2 := div_le_div_of_nonneg_left (hM x hx')
                (sq_pos_of_pos hp') (pow_le_pow_left₀ hp'.le hd' 2)
              _ = _ := by field_simp
          _ = ENNReal.ofReal ((k / 4)⁻¹ ^ 2) *
              ∫⁻ x in Ioc (R 0) R₀, ENNReal.ofReal (M x / x ^ 2) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ _ := by gcongr; exact (hpos 0).le
      exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint)
    have hcover : Ioc 0 R₀ ⊆ Ioc 0 (R 0) ∪ Ioc (R 0) R₀ := by
      intro x hx
      exact (le_total x (R 0)).elim (fun hh => Or.inl ⟨hx.1, hh⟩)
        (fun hh => by
          by_cases heq : x = R 0
          · exact Or.inl ⟨hx.1, heq.le⟩
          · exact Or.inr ⟨lt_of_le_of_ne hh (Ne.symm heq), hx.2⟩)
    exact (lintegral_mono_set hcover).trans_lt
      ((lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hinner.2, htop⟩))

end Terminal

end EmcsfAcExtension.Global
