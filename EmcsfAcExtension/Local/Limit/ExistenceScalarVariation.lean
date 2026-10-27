module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Limit.ExistenceEnvelopeBounds
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Infra.BV.Semicontinuity

/-! # Natural and covariant scalar variation in the primary limit

The incoming parallel factor uses the actual limiting potential. Uniform
potential convergence passes each phase primitive, so variation semicontinuity
applies directly to the frozen covariant representative.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem variation_le_limit {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {K : Set ℝ}
    {Bn : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hF : ∀ x ∈ K, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hB : Tendsto Bn atTop (𝓝 B)) (hb : ∀ n, eVariationOn (F n) K ≤ Bn n) :
    eVariationOn f K ≤ B := by
  apply (eVariationOn.le_liminf_of_tendsto hF).trans
  rw [← hB.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall hb) (by isBoundedDefault) (by isBoundedDefault)

/-- Pass the exact natural outgoing and frozen covariant incoming scalar
variations. The coefficient is explicitly `2*C²`, uniformly in time,
coupling, background, data and sequence. Each individual supremum is bounded
by `C²*d`; no phase is replaced by a different connection. -/
theorem StrongLimit.natural_covariant_variation_of_smoothBounds {C e T d : ℝ}
    {Sn : ℕ → Fields} {dn Mn : ℕ → ℝ} {S : Fields}
    (hT : 0 < T) (hC : 0 ≤ C) (hd : 0 ≤ d) (hdn : ∀ n, 0 ≤ dn n)
    (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hl : ∀ p ∈ triangle 0 T, S.lam p.1 p.2 ≠ 0)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 ≠ 0)
    (hvar : Tendsto dn atTop (𝓝 d))
    (hb : ∀ n, SmoothBounds C e T (dn n) (Mn n) (Sn n)) :
    (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
      (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤ ENNReal.ofReal (2 * C ^ 2 * d) := by
  have hbound : Tendsto (fun n => ENNReal.ofReal (C ^ 2 * dn n)) atTop
      (𝓝 (ENNReal.ofReal (C ^ 2 * d))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hvar.const_mul (C ^ 2))
  have hs n := scalar_variations_le_of_bounds hT hC (hdn n) (hc1 n) (hb n)
  have hout : (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) ≤ ENNReal.ofReal (C ^ 2 * d) := by
    apply iSup₂_le
    intro u hu
    exact variation_le_limit
      (fun v hv => hlim.tendsto_a_of_lam_ne_zero (p := (u, v)) ⟨hu.1, hv.1, hv.2⟩
        (hl (u, v) ⟨hu.1, hv.1, hv.2⟩)) hbound (fun n => (hs n).1 u hu)
  have hin : (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤ ENNReal.ofReal (C ^ 2 * d) := by
    apply iSup₂_le
    intro v hv
    apply variation_le_limit (hB := hbound) (hb := fun n => (hs n).2 v hv)
    intro u hu
    have hmaps : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) (triangle 0 T) :=
      fun s hs => ⟨hs.1, hs.2.trans hu.2, hv.2⟩
    have hcont n : ContinuousOn (fun s => (Sn n).A s v) (uIcc 0 u) := by
      rw [uIcc_of_le hu.1]
      exact (hc1 n).c1_A.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
          hmaps
    have hunif : TendstoUniformlyOn (fun n s => (Sn n).A s v) (fun s => S.A s v)
        atTop (uIcc 0 u) := by
      rw [uIcc_of_le hu.1]
      exact (hlim.unif_A.comp (fun s : ℝ => (s, v))).mono hmaps
    have hint := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      (Eventually.of_forall hcont) hunif
    have hphase := Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp hint).const_mul (I * (e : ℂ)))
    exact hphase.mul (hlim.tendsto_b_of_nu_ne_zero (p := (u, v)) ⟨hu.1, hu.2, hv.2⟩
      (hn (u, v) ⟨hu.1, hu.2, hv.2⟩))
  apply (add_le_add hout hin).trans_eq
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ C ^ 2 * d) (by positivity : 0 ≤ C ^ 2 * d)]
  congr 1
  ring

end EmcsfAcExtension.Local
