module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcing

/-! # Terminal adaptive profiles supply integrable forcing and tails

These are exactly the radial outputs of the approved internal project record terminal
handoff: continuous nonnegative mass, positive continuous adaptive radius,
both late smallness limits, and the finite reciprocal-square mass weight.
The logarithmic envelope is constructed explicitly. No forcing integral
or tail conclusion is assumed. Constants depend only on the fixed
coupling, envelope coefficient and reference radius, uniformly in tails.
Source: `charged_SF_new_version.tex:L1322–L1335`, approved internal project record (O8).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Every real integrable radius profile has a vanishing radius tail. This
uses absolute continuity of the Lebesgue integral, with no sign premise. -/
theorem radius_integral_tail_tendsto {f : ℝ → ℝ} {Rc : ℝ} (hRc : 0 < Rc)
    (hf : IntegrableOn f (Ioc 0 Rc)) :
    Tendsto (fun ρ => ∫ R in Ioc 0 ρ, f R) (𝓝[>] 0) (𝓝 0) := by
  have hb (ρ : ℝ) : (volume.restrict (Ioc 0 Rc)) (Ioc 0 ρ) ≤ ENNReal.ofReal ρ := by
    calc
      _ ≤ volume (Ioc 0 ρ) := Measure.restrict_le_self _
      _ = ENNReal.ofReal ρ := by simp [Real.volume_Ioc]
  have hz : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0 : ℝ)))
  have hμ : Tendsto (fun ρ : ℝ => (volume.restrict (Ioc 0 Rc)) (Ioc 0 ρ))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => bot_le) hb
  have ht := hf.tendsto_setIntegral_nhds_zero hμ
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT hRc] with ρ hρ
  rw [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_right hρ.2.le)]

/-- [node c:exterior#forcing-integrability]
The terminal adaptive profiles imply integrability of both `A=M/ell²`
and the literal five-term forcing. Their complete small-radius tails
tend to zero. The positive cutoff is selected from the proved smallness
limits; no forcing or tail hypothesis is introduced. -/
theorem forcing_integrability_of_terminal_profiles {e Ri C R₀ : ℝ}
    {M ell : ℝ → ℝ} (hRi : 0 < Ri) (hC : 0 ≤ C) (hR : 0 < R₀)
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hec : ContinuousOn ell (Ioc 0 R₀))
    (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (he : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hesmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤) :
    ∃ Rc ∈ Ioc 0 R₀,
      let L := fun R => C * (1 + Real.sqrt (Real.log (Ri / R)))
      IntegrableOn (fun R => M R / ell R ^ 2) (Ioc 0 Rc) ∧
      IntegrableOn (exteriorForcing e M ell L) (Ioc 0 Rc) ∧
      Tendsto (fun ρ => ∫ R in Ioc 0 ρ, M R / ell R ^ 2) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun ρ => ∫ R in Ioc 0 ρ, exteriorForcing e M ell L R) (𝓝[>] 0) (𝓝 0) := by
  let L := fun R => C * (1 + Real.sqrt (Real.log (Ri / R)))
  have hscale : Tendsto (fun R => L R ^ 2 * R ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [one_pow, one_mul, L] using logarithmic_scale_tendsto_zero Ri C 1 hRi
  have hlate : ∀ᶠ R in 𝓝[>] (0 : ℝ),
      M R / ell R < 1 ∧ ell R / R < 1 ∧ L R ^ 2 * R ^ 2 < 1 := by
    filter_upwards [hsmall.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)),
      hesmall.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)),
      hscale.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))] with R h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hlate
  change 0 < d at hd
  let Rc := min (R₀ / 2) (d / 2)
  have hRc : 0 < Rc := lt_min (by linarith) (by linarith)
  have hRcR : Rc ≤ R₀ := (min_le_left _ _).trans (by linarith)
  have hRcd : Rc < d := (min_le_right _ _).trans_lt (by linarith)
  have hsub : Ioc 0 Rc ⊆ Ioc 0 R₀ := Ioc_subset_Ioc_right hRcR
  have hlateR (R : ℝ) (hRR : R ∈ Ioc 0 Rc) := hdb ⟨hRR.1, hRR.2.trans_lt hRcd⟩
  have hel (R : ℝ) (hRR : R ∈ Ioc 0 Rc) : ell R ≤ R := by
    have hh := (div_lt_iff₀ hRR.1).mp (hlateR R hRR).2.1
    linarith only [hh]
  have hL0 (R : ℝ) : 0 ≤ L R := by dsimp [L]; positivity
  have hK (R : ℝ) (hRR : R ∈ Ioc 0 Rc) : L R * ell R ≤ 1 := by
    have hs := (hlateR R hRR).2.2
    have hh : L R * R ≤ 1 := by nlinarith only [hs]
    exact (mul_le_mul_of_nonneg_left (hel R hRR) (hL0 R)).trans hh
  have hMR (R : ℝ) (hRR : R ∈ Ioc 0 Rc) : 0 ≤ M R ∧ M R ≤ R := by
    refine ⟨hM R (hsub hRR), ?_⟩
    have hh := (div_le_iff₀ (he R (hsub hRR))).mp (hlateR R hRR).1.le
    exact (by simpa only [one_mul] using hh : M R ≤ ell R).trans (hel R hRR)
  have cA : ContinuousOn (fun R => M R / ell R ^ 2) (Ioc 0 R₀) :=
    hMc.div (hec.pow 2) (fun R hRR => pow_ne_zero _ (he R hRR).ne')
  have iA₀ : IntegrableOn (fun R => M R / ell R ^ 2) (Ioc 0 R₀) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (cA.aestronglyMeasurable measurableSet_Ioc) ?_).mp hAfinite.ne
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with R hRR
    exact div_nonneg (hM R hRR) (sq_nonneg _)
  have iA := iA₀.mono_set hsub
  have iG : IntegrableOn (exteriorForcing e M ell L) (Ioc 0 Rc) :=
    exteriorForcing_integrable_of_profiles hRc (hMc.mono hsub) (hec.mono hsub)
      (logarithmic_envelope_continuousOn hRi) iA
      (logarithmic_envelope_integrable hRi hRc)
      (logarithmic_envelope_sq_integrable hRi hRc) hMR
      (fun R hRR => he R (hsub hRR)) (fun R hRR => (hlateR R hRR).1.le)
      (fun R _ => hL0 R) hK
  exact ⟨Rc, ⟨hRc, hRcR⟩, iA, iG,
    radius_integral_tail_tendsto hRc iA, radius_integral_tail_tendsto hRc iG⟩

end EmcsfAcExtension.Global.Exterior
