module

public import EmcsfAcExtension.Global.Exterior.Frontier
public import EmcsfAcExtension.Global.Exterior.FrontierIntegrability
public import EmcsfAcExtension.Global.Calculus.Gauge
import EmcsfAcExtension.Infra.IntegralModulus

/-! # Uniform boundary tails from a common integrable majorant

The majorant is fixed before selecting a frontier or cylinder segment.
This elementary tail lemma preserves the uniformity in the cylinder radius
and final time required at `charged_SF_new_version.tex:L1405–L1408`. The covariant
variation bound uses the already established fixed-density chain rule.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
For an increasing real boundary, the norm of the speed-weighted complex
density has exactly the nonnegative exit integrand. The equality holds
for any chosen density, with no integrability or derivative regularity
premise. No constants occur. -/
theorem boundary_weighted_density_norm_eq_exit
    {a b : ℝ} {V : ℝ → ℝ} (hab : a ≤ b) (hm : MonotoneOn V (Icc a b))
    (W : ℝ → ℂ) :
    (∫ u in a..b, ‖deriv V u • W u‖) = ∫ u in a..b, deriv V u * ‖W u‖ := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hd : 0 ≤ deriv V u := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
    exact hm.derivWithin_nonneg
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd]

/-- [internal]
One integrable time majorant gives uniformly small norm integrals over
every sufficiently late proper interval and every dominated carrier.
The cutoff depends only on the majorant, its initial interval and the
tolerance; it precedes the interval and carrier quantifiers. -/
theorem uniform_interval_norm_tail_of_integrable_majorant
    {c : ℝ} (hc : c < 0) {G : ℝ → ℝ} (hG : IntegrableOn G (Ico c 0)) :
    ∀ ε > 0, ∃ u₀ ∈ Ioo c 0, ∀ a b : ℝ, u₀ ≤ a → a ≤ b → b < 0 →
      ∀ f : ℝ → ℂ, IntervalIntegrable f volume a b →
        (∀ u ∈ Icc a b, ‖f u‖ ≤ G u) → (∫ u in a..b, ‖f u‖) ≤ ε := by
  let G₀ : ℝ → ℝ := (Ico c 0).indicator G
  have hG₀ : Integrable G₀ := (integrable_indicator_iff measurableSet_Ico).2 hG
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_integral_norm_Icc_le hG₀ hε
  let u₀ := max (c / 2) (-δ / 2)
  have hu₀ : u₀ ∈ Ioo c 0 := ⟨lt_of_lt_of_le (by linarith only [hc]) (le_max_left _ _),
    max_lt (by linarith only [hc]) (by linarith only [hδ])⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro a b ha hab hb f hf hbound
  have hd : b - a ≤ δ := by
    have haa : -δ / 2 ≤ a := (le_max_right (c / 2) (-δ / 2)).trans ha
    linarith only [haa, hb, hδ]
  have hs : Icc a b ⊆ Ico c 0 := by
    intro u hu
    exact ⟨hu₀.1.le.trans (ha.trans hu.1), hu.2.trans_lt hb⟩
  have hnorm : (∫ u in a..b, ‖f u‖) ≤ ∫ u in a..b, ‖G₀ u‖ := by
    apply intervalIntegral.integral_mono_on hab hf.norm hG₀.intervalIntegrable.norm
    intro u hu
    rw [show G₀ u = G u from indicator_of_mem (hs hu) G, Real.norm_eq_abs]
    exact (hbound u hu).trans (le_abs_self _)
  have htail := hsmall (b - a) hd a
  rw [show a + (b - a) = b by ring] at htail
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at hnorm
  calc
    (∫ u in a..b, ‖f u‖) = ∫ u in Icc a b, ‖f u‖ := by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    _ ≤ ε := hnorm.trans htail

private theorem covariant_variation_le_of_chain
    {e : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {V : ℝ → ℝ} {a b : ℝ}
    {g w : ℝ → ℂ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval (fun u => f u (V u)) a b)
    (hA : IntervalIntegrable (fun u => S.A u (V u)) volume a b)
    (hg : IntervalIntegrable g volume a b) (hw : IntervalIntegrable w volume a b)
    (hd : ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => f x (V x))
      (g u + w u - I * e * S.A u (V u) * f u (V u)) u) :
    curveCovVar e S f id V a b ≤
      ENNReal.ofReal ((∫ u in a..b, ‖g u‖) + ∫ u in a..b, ‖w u‖) := by
  have hA' : IntervalIntegrable (fun u => S.A (id u) (V u) * deriv id u) volume a b := by
    simpa only [id_eq, deriv_id, mul_one] using hA
  have he := Calculus.curveCovVar_eq_integral (U := id) (V := V) (f := f) (e := e) (S := S)
    hab hf hA'
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hder := (ae_restrict_iff' measurableSet_uIcc).1 hd
  calc
    _ = ∫ u in a..b, ‖g u + w u‖ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hder] with u hu hum
      simp only [id_eq, deriv_id, Complex.ofReal_one, mul_one]
      rw [(hu (uIoc_subset_uIcc hum)).deriv, sub_add_cancel]
    _ ≤ ∫ u in a..b, ‖g u‖ + ‖w u‖ :=
      intervalIntegral.integral_mono_on hab (hg.add hw).norm (hg.norm.add hw.norm)
        (fun u _ => norm_add_le (g u) (w u))
    _ = _ := intervalIntegral.integral_add hg.norm hw.norm

/-- [internal]
Covariant variation on any proper increasing bi-Lipschitz boundary is at
most the incoming transport cost plus the outgoing exit cost. The density
is the canonical fixed-row representative. All AC and integrability
premises are derived from the frozen solution and the geometric boundary
data, so this estimate is ready for both frontier and cylinder tail
consumers. The coefficient is `1`, uniform in every input. -/
theorem boundary_covariant_variation_le {ui e a b : ℝ} {S : Fields} {V : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x) :
    curveCovVar e S S.a id V a b ≤ ENNReal.ofReal
      ((∫ u in a..b, ‖(-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
        ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
          (S.theta u (V u) / (S.lam u (V u) : ℂ)) + I * e * S.Q u (V u) * S.phi u (V u))‖) +
      ∫ u in a..b, ‖deriv V u • densityRepresentative e S a u (V u)‖) := by
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
  let g : ℝ → ℂ := fun u =>
    (-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
      ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
        (S.theta u (V u) / (S.lam u (V u) : ℂ)) + I * e * S.Q u (V u) * S.phi u (V u))
  have hcmap : ContinuousOn (fun u : ℝ => (u, V u)) (uIcc a b) :=
    continuousOn_id.prodMk hV.continuousOn
  have hmap : MapsTo (fun u : ℝ => (u, V u)) (uIcc a b)
      (origDomain ui ∩ {p | p.1 < p.2}) := fun u hu => ⟨hmem u hu, hproper u hu⟩
  have hG₀ := Calculus.continuousOn_normalized_incoming_source
    (K := origDomain ui ∩ {p | p.1 < p.2}) hS Subset.rfl
  have hG₁ := hG₀.comp hcmap hmap
  have hG : ContinuousOn (fun u => G u (V u)) (uIcc a b) := hG₁
  have hAc₀ := hS.cont_A.comp hcmap hmem
  have hAc : ContinuousOn (fun u => S.A u (V u)) (uIcc a b) := hAc₀
  have hfc₀ := (Calculus.continuousOn_a hS).comp hcmap hmem
  have hfc : ContinuousOn (fun u => S.a u (V u)) (uIcc a b) := hfc₀
  have hconn : ContinuousOn (fun u => I * e * S.A u (V u) * S.a u (V u)) (uIcc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn hAc).const_mul (I * e)).mul hfc
  have hgi : IntervalIntegrable g volume a b := by
    apply (hG.intervalIntegrable.add hconn.intervalIntegrable).congr_ae
    filter_upwards [] with u
    dsimp only [G, g]
    simp only [Fields.a, add_sub_cancel_left]
    ring
  have hc := boundary_ac_chain_rule hS hab hV hm ha hmem hproper
  exact covariant_variation_le_of_chain hab.le hc.1 hAc.intervalIntegrable hgi
    (boundary_weighted_density_integrable hS hab hV hm ha hmem hproper)
    (frontier_chain_identity hS hab hV hm ha hmem hproper)

end EmcsfAcExtension.Global.Exterior
