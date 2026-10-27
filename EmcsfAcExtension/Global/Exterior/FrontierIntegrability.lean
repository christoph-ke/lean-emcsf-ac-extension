module

public import EmcsfAcExtension.Global.Exterior.Frontier
import EmcsfAcExtension.Infra.AC.Complex

/-! # Boundary density integrability and the covariant chain identity

The selected fixed-density representative is used at every boundary point.
Absolute continuity is proved through the improved-label route. The incoming
source is continuous, and subtracting it from the AC trace derivative proves
integrability of the weighted outgoing density. A local positive speed lower
bound then gives integrability of the density itself.
Source: `charged_SF_new_version.tex:L1347–L1355`, L1413–L1415.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
A positive inverse-distance estimate gives the precise anti-Lipschitz
map on the boundary interval. The local coefficient `m` is fixed before
both points vary; no terminal uniform inverse bound is asserted. -/
theorem boundary_antilipschitz_of_inverse_distance
    {V : ℝ → ℝ} {a b m : ℝ} (hm : 0 < m)
    (h : ∀ u ∈ uIcc a b, ∀ w ∈ uIcc a b,
      m * dist u w ≤ dist (V u) (V w)) :
    AntilipschitzWith (Real.toNNReal m⁻¹) ((uIcc a b).domRestrict V) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro u w
  change dist (u : ℝ) (w : ℝ) ≤
    (Real.toNNReal m⁻¹ : ℝ) * dist (V u) (V w)
  rw [Real.coe_toNNReal _ (inv_pos.mpr hm).le]
  calc
    _ ≤ dist (V u) (V w) / m := (le_div_iff₀ hm).2 (by
      simpa only [mul_comm] using h u u.2 w w.2)
    _ = _ := by ring

variable {ui e : ℝ} {S : Fields} {a b : ℝ} {V : ℝ → ℝ} {K L : ℝ≥0}

private theorem integrable_remainder_of_ac_chain {f g w : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt f (g u + w u) u) :
    IntervalIntegrable w volume a b := by
  apply (hf.intervalIntegrable_deriv_complex.sub hg).congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hd' := (ae_restrict_iff' measurableSet_uIcc).1 hd
  filter_upwards [hd'] with u hu hum
  rw [(hu (uIoc_subset_uIcc hum)).deriv]
  abel

/-- [node c:exterior#frontier-chain-identity]
The covariant chain identity on every proper increasing bi-Lipschitz
boundary, hence in particular on each proper frontier segment. The
connection is displayed as `-ieA f` in the ordinary derivative. The outgoing
derivative is the fixed representative anchored at `a`. No constant occurs. -/
theorem frontier_chain_identity (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x) :
    ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => S.a x (V x))
      ((-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
        ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
          (S.theta u (V u) / (S.lam u (V u) : ℂ)) +
          I * e * S.Q u (V u) * S.phi u (V u)) +
        deriv V u • densityRepresentative e S a u (V u) -
        I * e * S.A u (V u) * S.a u (V u)) u := by
  have hc := boundary_ac_chain_rule hS hab hV hm ha hmem hproper
  filter_upwards [hc.2] with u hu
  apply hu.congr_deriv
  simp only [Fields.a, add_sub_cancel_left]
  ring

/-- [internal]
The weighted boundary density is locally integrable on an entire proper
boundary segment. This is derived from the AC chain rule and continuous
incoming transport, without an integrability hypothesis on the boundary
evaluation. The explicit Lipschitz constants are local to the segment. -/
theorem boundary_weighted_density_integrable (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x) :
    IntervalIntegrable (fun u => deriv V u • densityRepresentative e S a u (V u)) volume a b := by
  let G : ℝ → ℝ → ℂ := fun u v =>
    (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) * (S.a u v - S.phi u v) +
      I * e * (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        S.Q u v * S.phi u v - I * e * S.A u v * S.a u v
  have hc := boundary_ac_chain_rule hS hab hV hm ha hmem hproper
  have hG := Calculus.continuousOn_normalized_incoming_source
    (K := origDomain ui ∩ {p | p.1 < p.2}) hS Subset.rfl
  have hcmap : ContinuousOn (fun u : ℝ => (u, V u)) (uIcc a b) :=
    continuousOn_id.prodMk hV.continuousOn
  have hmap : MapsTo (fun u : ℝ => (u, V u)) (uIcc a b)
      (origDomain ui ∩ {p | p.1 < p.2}) := fun u hu => ⟨hmem u hu, hproper u hu⟩
  have hg₀ := hG.comp hcmap hmap
  have hg : ContinuousOn (fun u => G u (V u)) (uIcc a b) := hg₀
  have hgi : IntervalIntegrable (fun u => G u (V u)) volume a b := hg.intervalIntegrable
  have hdi : ∀ᵐ u ∂volume.restrict (uIcc a b), HasDerivAt (fun x => S.a x (V x))
      (G u (V u) + deriv V u • densityRepresentative e S a u (V u)) u := hc.2
  exact integrable_remainder_of_ac_chain (f := fun x => S.a x (V x))
    (g := fun u => G u (V u)) (w := fun u => deriv V u • densityRepresentative e S a u (V u))
    hc.1 hgi hdi

/-- [internal]
A local positive lower speed bound gives integrability of the prescribed
boundary density itself, as well as its exit-weighted version. The lower
bound `m` belongs to the proper segment; it is supplied for frontier and
cylinder segments by their geometric speed estimates. It is not a global
terminal assumption. This establishes the integrability part of the node;
the stopped-history Tonelli formula is a separate moving-domain obligation. -/
theorem boundary_derivative_integrability_of_speed (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x)
    {m : ℝ} (hm0 : 0 < m)
    (hspd : ∀ᵐ u ∂volume.restrict (Icc a b), m ≤ deriv V u) :
    IntervalIntegrable (fun u => densityRepresentative e S a u (V u)) volume a b ∧
      IntervalIntegrable (fun u => deriv V u • densityRepresentative e S a u (V u)) volume a b := by
  have hi := boundary_weighted_density_integrable hS hab hV hm ha hmem hproper
  have hii := (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1 hi
  let W : ℝ → ℂ := fun u => deriv V u • densityRepresentative e S a u (V u)
  have hWi : IntegrableOn W (Icc a b) := hii
  have hsm : AEStronglyMeasurable (fun u => (deriv V u)⁻¹ • W u)
      (volume.restrict (Icc a b)) :=
    ((measurable_deriv V).inv.aestronglyMeasurable).smul hWi.aestronglyMeasurable
  have hIi : IntegrableOn (fun u => (deriv V u)⁻¹ • W u) (Icc a b) := by
    apply Integrable.mono' (hWi.norm.const_mul m⁻¹) hsm
    filter_upwards [hspd] with u hu
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hm0.le.trans hu))]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hm0 hu) (norm_nonneg _)
  have hWii : IntegrableOn (fun u => densityRepresentative e S a u (V u)) (Icc a b) := by
    apply hIi.congr
    filter_upwards [hspd] with u hu
    dsimp only [W]
    rw [smul_smul, inv_mul_cancel₀ (hm0.trans_le hu).ne', one_smul]
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).2 hWii, hi⟩

/-- [internal]
The local geometric inverse-distance bound forces a positive a.e. speed.
The coefficient `m` is fixed before the two parameters and depends only
on the chosen proper boundary segment. -/
theorem boundary_speed_lower_of_inverse_distance
    {a b m : ℝ} {V : ℝ → ℝ} {K : ℝ≥0}
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b))
    (hdist : ∀ u ∈ uIcc a b, ∀ w ∈ uIcc a b,
      m * dist u w ≤ dist (V u) (V w)) :
    ∀ᵐ u ∂volume.restrict (Icc a b), m ≤ deriv V u := by
  have hm' : MonotoneOn V (Icc a b) := by simpa only [uIcc_of_le hab.le] using hm
  have hsubtract : MonotoneOn (fun u => V u - m * u) (Icc a b) := by
    intro u hu w hw huw
    have hh := hdist u (by simpa only [uIcc_of_le hab.le] using hu)
      w (by simpa only [uIcc_of_le hab.le] using hw)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huw), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (hm' hu hw huw))] at hh
    nlinarith only [hh]
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hV.absolutelyContinuousOnInterval.ae_differentiableAt]
      with u hu hd
  have hum : u ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact Ioo_subset_Icc_self hu
  have hh : 0 ≤ deriv (fun u => V u - m * u) u := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
    exact hsubtract.derivWithin_nonneg
  have hd' : HasDerivAt (fun x => V x - m * x) (deriv V u - m) u := by
    simpa only [Pi.sub_apply, id_eq, mul_one] using!
      (hd hum).hasDerivAt.sub ((hasDerivAt_id u).const_mul m)
  rw [hd'.deriv] at hh
  linarith only [hh]

/-- [node c:exterior#boundary-derivative-integrability]
The prescribed derivative and its speed-weighted version are integrable
on every proper Lipschitz monotone boundary with a positive geometric
inverse-distance bound. The speed bound is derived here. Frontier and
cylinder geometry supply these local constants; neither density
integrability nor a derivative trace is assumed. Stopping and Tonelli
for the same representative are proved in `VariationTransport` and
`VariationTailsExit`. -/
theorem boundary_derivative_integrability
    {m : ℝ} (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hV : LipschitzOnWith K V (uIcc a b))
    (hm : MonotoneOn V (uIcc a b)) (hm0 : 0 < m)
    (hdist : ∀ u ∈ uIcc a b, ∀ w ∈ uIcc a b,
      m * dist u w ≤ dist (V u) (V w))
    (hmem : ∀ x ∈ uIcc a b, (x, V x) ∈ origDomain ui)
    (hproper : ∀ x ∈ uIcc a b, x < V x) :
    IntervalIntegrable (fun u => densityRepresentative e S a u (V u)) volume a b ∧
      IntervalIntegrable (fun u => deriv V u • densityRepresentative e S a u (V u)) volume a b :=
  boundary_derivative_integrability_of_speed hS hab hV hm
    (boundary_antilipschitz_of_inverse_distance hm0 hdist) hmem hproper hm0
    (boundary_speed_lower_of_inverse_distance hab hV hm hdist)

end EmcsfAcExtension.Global.Exterior
