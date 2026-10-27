module

public import EmcsfAcExtension.Global.Exterior.Variation
public import EmcsfAcExtension.Infra.Gronwall

/-! # Fixed-row tails and the variation Grönwall estimate

These are the analytic steps M4 and D1–D3 of approved internal project record,
`charged_SF_new_version.tex:L1337–L1416`. Every multiplier is displayed. In the
fixed-row argument the initial density is merely L¹; no modulus uniform
over the choice of anchor row is assumed.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] An integrable time forcing has a vanishing terminal
interval integral. Its complete profile is fixed before the cutoff varies. -/
theorem time_integral_tail_tendsto {f : ℝ → ℝ} {c : ℝ} (hc : c < 0)
    (hf : IntervalIntegrable f volume c 0) :
    Tendsto (fun u => ∫ s in u..0, f s) (𝓝[<] 0) (𝓝 0) := by
  have hi : IntegrableOn f (uIcc c 0) := by
    rw [uIcc_of_le hc.le]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hc.le).1 hf
  have hcont := intervalIntegral.continuousOn_primitive_interval_left hi
  have hid : Tendsto (fun u : ℝ => u) (𝓝[<] 0) (𝓝[uIcc c 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨continuousWithinAt_id.tendsto, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hc] with u hu
    rw [uIcc_of_le hc.le]
    exact ⟨hu.1.le, hu.2.le⟩
  have hh := (hcont 0 right_mem_uIcc).tendsto.comp hid
  have hh' : Tendsto (fun u => ∫ s in u..0, f s) (𝓝[<] 0)
      (𝓝 (∫ s in (0 : ℝ)..0, f s)) := by
    apply hh.congr'
    exact Eventually.of_forall fun u => by simp only [Function.comp_apply]
  simpa only [intervalIntegral.integral_same] using hh'

/-- [internal]
An L¹ density on one fixed proper outgoing interval has a vanishing
terminal label tail. This uses only the density on that row. -/
theorem fixed_row_norm_tail_tendsto {w : ℝ → ℂ} {c : ℝ} {t : ℝ → ℝ}
    (hc : c ≤ 0) (hw : IntervalIntegrable w volume c 0)
    (ht : Tendsto t (𝓝[<] 0) (𝓝 0))
    (hmem : ∀ᶠ u in 𝓝[<] (0 : ℝ), t u ∈ Icc c 0) :
    Tendsto (fun u => ∫ v in t u..0, ‖w v‖) (𝓝[<] 0) (𝓝 0) := by
  have hi : IntegrableOn (fun v => ‖w v‖) (uIcc c 0) := by
    rw [uIcc_of_le hc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hc).1 hw.norm
  have hc' := intervalIntegral.continuousOn_primitive_interval_left hi
  have ht' : Tendsto t (𝓝[<] 0) (𝓝[uIcc c 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨ht, ?_⟩
    simpa only [uIcc_of_le hc] using hmem
  have hh := (hc' 0 (right_mem_uIcc : (0 : ℝ) ∈ uIcc c 0)).tendsto.comp ht'
  have hh' : Tendsto (fun u => ∫ v in t u..0, ‖w v‖) (𝓝[<] 0)
      (𝓝 (∫ v in (0 : ℝ)..0, ‖w v‖)) := by
    apply hh.congr'
    exact Eventually.of_forall fun u => by simp only [Function.comp_apply]
  simpa only [intervalIntegral.integral_same] using hh'

/-- [internal]
The two-stage limit argument for a nonnegative quantity: choose one late
anchor making the common forcing tail small, then take the L¹ tail on
that fixed row. The coefficient `P` is fixed before both row choices. -/
theorem tendsto_zero_of_fixed_row_estimates {V T : ℝ → ℝ}
    {D : ℝ → ℝ → ℝ} {c P : ℝ} (hc : c < 0) (_hP : 0 ≤ P)
    (hV : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 ≤ V u)
    (hT : Tendsto T (𝓝[<] 0) (𝓝 0))
    (hD : ∀ s ∈ Ioo c 0, Tendsto (D s) (𝓝[<] 0) (𝓝 0))
    (hest : ∀ s ∈ Ioo c 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), V u ≤ P * D s u + T s) :
    Tendsto V (𝓝[<] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : ∀ᶠ s in 𝓝[<] (0 : ℝ), s ∈ Ioo c 0 ∧ T s < ε / 2 := by
    filter_upwards [Ioo_mem_nhdsLT hc,
      hT.eventually (Iio_mem_nhds (half_pos hε))] with s hs hTs
    exact ⟨hs, hTs⟩
  obtain ⟨s, hs, hTs⟩ := hs.exists
  have hPD : Tendsto (fun u => P * D s u) (𝓝[<] 0) (𝓝 0) :=
    by simpa only [mul_zero] using (hD s hs).const_mul P
  have hsmall : ∀ᶠ u in 𝓝[<] (0 : ℝ), P * D s u < ε / 2 :=
    hPD.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hV, hest s hs, hsmall] with u hu he hd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hu]
  linarith only [he, hd, hTs]

/-- [internal]
The field-level consumer of the fixed-proper-row Duhamel estimate D2.
The forcing tail tends to zero independently of the anchor. The density
on each anchor row is the ordinary a.e. derivative of the actual AC field;
its L¹ property is derived from `OriginalData`. -/
theorem outgoing_variation_decay_of_duhamel {ui e uc P : ℝ} {S : Fields}
    (h : OriginalData ui e S) (t T : ℝ → ℝ) (huc : uc ∈ Ioo ui 0)
    (hP : 0 ≤ P) (ht : Tendsto t (𝓝[<] 0) (𝓝 0))
    (hrow : ∀ u ∈ Ico uc 0, u < t u ∧ t u ≤ 0)
    (hmono : MonotoneOn t (Ico uc 0))
    (hT : Tendsto T (𝓝[<] 0) (𝓝 0))
    (hD : ∀ s ∈ Ioo uc 0, ∀ u ∈ Ioo s 0,
      (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤
        P * (∫ v in t u..0, ‖deriv (S.a s) v‖) + T s) :
    Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0) := by
  apply tendsto_zero_of_fixed_row_estimates huc.2 hP
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hT
  · intro s hs
    have hsr := hrow s ⟨hs.1.le, hs.2⟩
    have hseg : outSeg s (t s) 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hsr.2).2
        ⟨huc.1.le.trans hs.1.le, hs.2, hsr.1.le, le_rfl⟩
    have hw := (h.solution.ac_out s (t s) 0 hsr.2 hseg).2.2.2.2
    apply fixed_row_norm_tail_tendsto hsr.2 hw.intervalIntegrable_deriv_complex ht
    filter_upwards [Ioo_mem_nhdsLT hs.2] with u hu
    exact ⟨hmono ⟨hs.1.le, hs.2⟩ ⟨hs.1.le.trans hu.1.le, hu.2⟩ hu.1.le,
      (hrow u ⟨hs.1.le.trans hu.1.le, hu.2⟩).2⟩
  · intro s hs
    filter_upwards [Ioo_mem_nhdsLT hs.2] with u hu
    exact hD s hs u hu

/-- [internal]
Integral Grönwall with one constant valid on every later proper row.
The coefficient and forcing are integrable on the full terminal interval.
The bound depends only on their complete integrals and the entry value,
uniformly in the observation row. -/
theorem uniform_bound_of_moving_modulus {V k q : ℝ → ℝ} {c : ℝ}
    (hc : c < 0) (hVc : 0 ≤ V c)
    (hcont : ∀ b ∈ Ico c 0, ContinuousOn V (Icc c b))
    (hk : IntervalIntegrable k volume c 0) (hq : IntervalIntegrable q volume c 0)
    (hk₀ : ∀ u ∈ Ico c 0, 0 ≤ k u) (hq₀ : ∀ u ∈ Ico c 0, 0 ≤ q u)
    (hmod : ∀ u ∈ Ico c 0,
      V u ≤ V c + ∫ s in c..u, (k s * V s + q s)) :
    ∀ u ∈ Ico c 0, V u ≤
      (V c + ∫ s in c..0, q s) * Real.exp (∫ s in c..0, k s) := by
  intro u hu
  have hk₀ae : ∀ᵐ s ∂volume.restrict (Icc c 0), 0 ≤ k s := by
    rw [← restrict_Ico_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ico).mono fun s hs => hk₀ s hs
  have hq₀ae : ∀ᵐ s ∂volume.restrict (Icc c 0), 0 ≤ q s := by
    rw [← restrict_Ico_eq_restrict_Icc]
    exact (ae_restrict_mem measurableSet_Ico).mono fun s hs => hq₀ s hs
  have hsub : uIcc c u ⊆ uIcc c 0 := by
    rw [uIcc_of_le hu.1, uIcc_of_le hc.le]
    exact Icc_subset_Icc le_rfl hu.2.le
  have hku := hk.mono_set hsub
  have hqu := hq.mono_set hsub
  have hcv := hcont u hu
  have hkv : IntervalIntegrable (fun s => k s * V s) volume c u :=
    hku.mul_continuousOn (by rwa [uIcc_of_le hu.1])
  have hg := le_exp_integral_of_le_integral_forcing hu.1 hcv hku hqu
    ((ae_restrict_mem measurableSet_Icc).mono fun s hs => hk₀ s ⟨hs.1, hs.2.trans_lt hu.2⟩)
    ((ae_restrict_mem measurableSet_Icc).mono fun s hs => hq₀ s ⟨hs.1, hs.2.trans_lt hu.2⟩)
    (C := V c) (by
      intro x hx
      have hx' : x ∈ Ico c 0 := ⟨hx.1, hx.2.trans_lt hu.2⟩
      have hsubx : uIcc c x ⊆ uIcc c u := by
        rw [uIcc_of_le hx.1, uIcc_of_le hu.1]
        exact Icc_subset_Icc le_rfl hx.2
      have hm := hmod x hx'
      rw [intervalIntegral.integral_add (hkv.mono_set hsubx) (hqu.mono_set hsubx)] at hm
      linarith only [hm])
    u ⟨hu.1, le_rfl⟩
  have hqle : (∫ s in c..u, q s) ≤ ∫ s in c..0, q s :=
    intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2.le
      (by rwa [restrict_Ioc_eq_restrict_Icc]) hq
  have hkle : (∫ s in c..u, k s) ≤ ∫ s in c..0, k s :=
    intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2.le
      (by rwa [restrict_Ioc_eq_restrict_Icc]) hk
  exact hg.trans (mul_le_mul (add_le_add le_rfl hqle) (Real.exp_le_exp.mpr hkle)
    (Real.exp_pos _).le (add_nonneg hVc
      (intervalIntegral.integral_nonneg_of_ae_restrict hc.le hq₀ae)))

end EmcsfAcExtension.Global.Exterior
