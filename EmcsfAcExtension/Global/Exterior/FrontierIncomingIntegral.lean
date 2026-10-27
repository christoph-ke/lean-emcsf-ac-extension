module

public import EmcsfAcExtension.Global.Exterior.FrontierIncomingTails

/-! # Complete incoming transport integrals and endpoint tails

These lemmas pass from proper segments to the missing terminal endpoint.
They keep one fixed carrier and one common integrable majorant; no value
or trace at the missing endpoint is assumed. Source:
`charged_SF_new_version.tex:L1356–L1362`, L1416, approved internal project record (I1)–(I3).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Continuity on all proper initial segments gives continuity on the whole
half-open terminal interval. No uniform continuity modulus is required.
No constants occur. -/
theorem continuousOn_boundary_Ico_of_proper_segments
    {c : ℝ} {V : ℝ → ℝ}
    (hV : ∀ b, c ≤ b → b < 0 → ContinuousOn V (Icc c b)) :
    ContinuousOn V (Ico c 0) := by
  intro u hu
  have hub : u < u / 2 := by linarith only [hu.2]
  have hb : u / 2 < 0 := by linarith only [hu.2]
  apply (hV (u / 2) (hu.1.trans hub.le) hb u ⟨hu.1, hub.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hub)] with x hx hxb
  exact ⟨hx.1, hxb.le⟩

/-- [internal]
A common integrable exterior majorant proves integrability of the complete
incoming covariant transport on any continuous proper terminal carrier.
The majorant precedes the carrier and controls every point of the exterior;
there are no carrier-dependent constants. -/
theorem boundary_incoming_integrable_of_majorant
    {ui e c : ℝ} {S : Fields} {ell H V : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui))
    (hH : IntegrableOn H (Ico c 0)) (hV : ContinuousOn V (Ico c 0))
    (hmem : ∀ u ∈ Ico c 0, (u, V u) ∈ adaptiveExterior S ui c ell)
    (hp : ∀ u ∈ Ico c 0, u < V u)
    (hbound : ∀ p ∈ adaptiveExterior S ui c ell,
      ‖(-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
        ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
          (S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) +
          I * e * S.Q p.1 p.2 * S.phi p.1 p.2)‖ ≤ H p.1) :
    IntegrableOn (fun u =>
      (-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
        ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
          (S.theta u (V u) / (S.lam u (V u) : ℂ)) +
          I * e * S.Q u (V u) * S.phi u (V u))) (Ico c 0) := by
  have hc := continuousOn_covariant_incoming_source hS hV (fun u hu => (hmem u hu).1) hp
  apply Integrable.mono' hH (hc.aestronglyMeasurable measurableSet_Ico)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  exact hbound (u, V u) (hmem u hu)

/-- [internal]
The full norm integral of a fixed L¹ carrier has a vanishing terminal tail.
The endpoint is excluded and the representative is fixed throughout.
No constants or uniform continuity assumptions occur. -/
theorem norm_integral_terminal_tail_tendsto
    {c : ℝ} {g : ℝ → ℂ} (hc : c < 0) (hg : IntegrableOn g (Ico c 0)) :
    Tendsto (fun a => ∫ u in Ico a 0, ‖g u‖) (𝓝[<] 0) (𝓝 0) := by
  have hb (a : ℝ) : (volume.restrict (Ico c 0)) (Ico a 0) ≤ ENNReal.ofReal (-a) := by
    calc
      _ ≤ volume (Ico a 0) := Measure.restrict_le_self _
      _ = ENNReal.ofReal (-a) := by simp [Real.volume_Ico]
  have hr : Tendsto (fun a : ℝ => -a) (𝓝[<] 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun a : ℝ => ENNReal.ofReal (-a)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hr
  have hμ : Tendsto (fun a : ℝ => (volume.restrict (Ico c 0)) (Ico a 0))
      (𝓝[<] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => bot_le) hb
  have ht := hg.norm.tendsto_setIntegral_nhds_zero hμ
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT hc] with a ha
  rw [Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (Ico_subset_Ico_left ha.1.le)]

end EmcsfAcExtension.Global.Exterior
