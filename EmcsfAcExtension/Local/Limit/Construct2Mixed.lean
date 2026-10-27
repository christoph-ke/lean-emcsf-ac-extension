module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.Mixed.TriangleCauchy

/-! # Measurable mixed-density error envelopes

Measurable liminf envelopes of continuous pairwise differences dominate the
errors against the fiber limits. Fatou and the original mixed Cauchy estimate
give convergence of their masses. This avoids taking a measurability claim
for an uncountable supremum of an arbitrary measurable representative.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem errors_of_fiber_limit {T : ℝ} {a b : ℝ → ℝ}
    {F : ℕ → ℝ → ℝ → ℂ} {f : ℝ → ℝ → ℂ} {ns : ℕ → ℕ} {N : Set ℝ}
    (hns : StrictMono ns) (hN : volume N = 0)
    (hp : ∀ n m, Measurable ((Icc (0 : ℝ) T).indicator
      (fun v => ⨆ u ∈ Icc (a v) (b v), ‖F n u v - F m u v‖ₑ)))
    (hc : ∀ ρ > (0 : ℝ), ∃ L : ℕ, ∀ n ≥ L, ∀ m ≥ L,
      (∫⁻ v in Icc 0 T, ⨆ u ∈ Icc (a v) (b v), ‖F n u v - F m u v‖ₑ) < ENNReal.ofReal ρ)
    (hlim : ∀ v ∈ Icc 0 T, v ∉ N → ∀ u ∈ Icc (a v) (b v),
      Tendsto (fun l => F (ns l) u v) atTop (𝓝 (f u v))) :
    ∃ D : ℕ → ℝ → ℝ≥0∞, (∀ n, Measurable (D n)) ∧
      Tendsto (fun n => ∫⁻ v in Icc 0 T, D n v) atTop (𝓝 0) ∧
      ∀ n, ∀ᵐ v ∂volume.restrict (Icc 0 T), ∀ u ∈ Icc (a v) (b v),
        ‖F n u v - f u v‖ₑ ≤ D n v := by
  classical
  let P n m := (Icc (0 : ℝ) T).indicator
    (fun v => ⨆ u ∈ Icc (a v) (b v), ‖F n u v - F m u v‖ₑ)
  let D n v := liminf (fun l => P n (ns l) v) atTop
  have hD n : Measurable (D n) := Measurable.liminf (fun l => hp n (ns l))
  have hfat n : (∫⁻ v in Icc 0 T, D n v) ≤
      liminf (fun l => ∫⁻ v in Icc 0 T, P n (ns l) v) atTop :=
    lintegral_liminf_le' (fun l => (hp n (ns l)).aemeasurable)
  have hmass : Tendsto (fun n => ∫⁻ v in Icc 0 T, D n v) atTop (𝓝 0) := by
    apply ENNReal.tendsto_atTop_zero.2
    intro ε hε
    by_cases htop : ε = ⊤
    · exact ⟨0, fun _ _ => htop ▸ le_top⟩
    obtain ⟨L, hL⟩ := hc ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    refine ⟨L, fun n hn => (hfat n).trans ?_⟩
    rw [liminf_eq_iSup_iInf_of_nat]
    apply iSup_le
    intro i
    obtain ⟨l, hli, hlL⟩ := ((eventually_ge_atTop i).and
      (hns.tendsto_atTop.eventually (eventually_ge_atTop L))).exists
    apply iInf₂_le_of_le l hli
    have heq : (∫⁻ v in Icc 0 T, P n (ns l) v) =
        ∫⁻ v in Icc 0 T, ⨆ u ∈ Icc (a v) (b v), ‖F n u v - F (ns l) u v‖ₑ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      exact indicator_of_mem hv _
    rw [heq]
    exact (hL n hn (ns l) hlL).le.trans_eq (ENNReal.ofReal_toReal htop)
  refine ⟨D, hD, hmass, ?_⟩
  intro n
  have hgood : ∀ᵐ v ∂volume, v ∉ N := by simpa [ae_iff] using hN
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hgood] with v hv hNv u hu
  have hnorm : Tendsto (fun l => ‖F n u v - F (ns l) u v‖ₑ) atTop
      (𝓝 ‖F n u v - f u v‖ₑ) := (tendsto_const_nhds.sub (hlim v hv hNv u hu)).enorm
  rw [← hnorm.liminf_eq]
  apply liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
  exact Eventually.of_forall fun l => by
    dsimp only [P]
    rw [indicator_of_mem hv]
    exact le_iSup₂_of_le u hu le_rfl

/-- Construct both measurable densities and measurable vanishing error
envelopes from the actual two mixed Cauchy estimates. The coefficient in
every domination is one, uniformly in time, coupling and all sequence sizes.
This helper precedes identification with the frozen derivatives. -/
theorem exists_mixed_densities_with_errors_of_cauchy {e T : ℝ} {Sn : ℕ → Fields}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hj : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) < ENNReal.ofReal ρ)
    (hk : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ) :
    ∃ (j k : ℝ → ℝ → ℂ) (Dj Dk : ℕ → ℝ → ℝ≥0∞),
      Measurable (Function.uncurry j) ∧ Measurable (Function.uncurry k) ∧
      (∀ n, Measurable (Dj n)) ∧ (∀ n, Measurable (Dk n)) ∧
      Tendsto (fun n => ∫⁻ v in Icc 0 T, Dj n v) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ u in Icc 0 T, Dk n u) atTop (𝓝 0) ∧
      (∀ n, ∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T),
        ‖jC1 (triangle 0 T) (Sn n) u v - j u v‖ₑ ≤ Dj n v) ∧
      (∀ n, ∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v),
        ‖kC1 e (triangle 0 T) (Sn n) u v - k u v‖ₑ ≤ Dk n u) ∧
      Tendsto (fun n => ∫⁻ v in Icc 0 T,
        outEnv 0 (fun u v => jC1 (triangle 0 T) (Sn n) u v - j u v) v) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ u in Icc 0 T,
        inEnv T (fun u v => kC1 e (triangle 0 T) (Sn n) u v - k u v) u) atTop (𝓝 0) := by
  obtain ⟨nj, Nj, j, J, hnj, _, hNj, _, hjm, _, _, hjseq, _, _, hjlim, _⟩ :=
    Mixed.exists_outgoing_mixed_limit hT.le (fun n => (hS n).continuousOn_jC1 hT) hj
  obtain ⟨nk, Nk, k, K, hnk, _, hNk, _, hkm, _, _, hkseq, _, _, hklim, _⟩ :=
    Mixed.exists_incoming_mixed_limit hT.le (fun n => (hS n).continuousOn_kC1 hT) hk
  obtain ⟨Dj, hDjm, hDjl, hjdom⟩ := errors_of_fiber_limit hnj hNj
    (fun n m => measurable_indicator_normEnvelope
      ((hS n).continuousOn_jC1 hT |>.sub ((hS m).continuousOn_jC1 hT))) hj
    (fun v hv hNv u hu => (hjseq v hv hNv).tendsto_at hu)
  obtain ⟨Dk, hDkm, hDkl, hkdom⟩ := errors_of_fiber_limit
    (F := fun n v u => kC1 e (triangle 0 T) (Sn n) u v)
    (f := fun v u => k u v) hnk hNk
    (fun n m => Mixed.measurable_indicator_incoming_envelope hT.le
      ((hS n).continuousOn_kC1 hT |>.sub ((hS m).continuousOn_kC1 hT))) hk
    (fun u hu hNu v hv => (hkseq u hu hNu).tendsto_at hv)
  refine ⟨j, k, Dj, Dk, hjm, hkm, hDjm, hDkm, hDjl, hDkl, ?_, ?_, hjlim, hklim⟩
  · intro n u hu
    have hh := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hu.1 le_rfl) (hjdom n)
    filter_upwards [hh, ae_restrict_mem measurableSet_Icc] with v hv hmem
    exact hv u ⟨hu.1, hmem.1⟩
  · intro n v hv
    have hh := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl hv.2) (hkdom n)
    filter_upwards [hh, ae_restrict_mem measurableSet_Icc] with u hu hmem
    exact hu v ⟨hmem.2, hv.2⟩

end EmcsfAcExtension.Local
