module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Almost-everywhere speed of the adaptive frontier

The radius has its original continuous partial derivatives. The adaptive
profile is differentiated only almost everywhere; terminal-radius
substitution pulls that exceptional set back to a null set of labels.
-/

public section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The terminal radius has its literal incoming derivative at each proper
interior label. This uses only the frozen incoming radius equation and
continuity of the incoming expansion on proper sections. -/
theorem terminal_radius_hasDerivAt (h : OriginalData ui e S) {u : ℝ} (hu : u ∈ Ioo ui 0) :
    HasDerivAt (fun x => S.r x 0) (S.nu u 0) u := by
  let a := (ui + u) / 2
  let b := u / 2
  have hau : a < u := by dsimp [a]; linarith [hu.1]
  have hub : u < b := by dsimp [b]; linarith [hu.2]
  have hia : ui ≤ a := by dsimp [a]; linarith [hu.1]
  have hb : b < 0 := by dsimp [b]; linarith [hu.2]
  have hs : inSeg a b 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff (hau.trans hub).le).2 ⟨hia, hb, hb.le, le_rfl⟩
  apply Local.hasDerivAt_of_integralForm_interior ⟨hau, hub⟩
    ((Calculus.continuousOn_in_section h.solution.cont_nu hs).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (h.solution.eq_in c d 0 hcd (hd.trans hb)
    (fun _ hp => hs (inSeg_subset_inSeg hc.le hd.le hp))).1

/-- [internal]
At every original interior point the radius has the full derivative
with components `ν, λ`. The C¹ consequence of the frozen class is used
on a proper triangle entirely inside the original development. -/
theorem radius_hasFDerivAt_of_interior (h : OriginalData ui e S) {u v : ℝ}
    (hui : ui < u) (huv : u < v) (hv : v < 0) :
    HasFDerivAt (Function.uncurry S.r)
      (S.nu u v • ContinuousLinearMap.fst ℝ ℝ ℝ +
        S.lam u v • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, v) := by
  let a := (ui + u) / 2
  let b := v / 2
  have hau : a < u := by dsimp [a]; linarith
  have hia : ui ≤ a := by dsimp [a]; linarith
  have hvb : v < b := by dsimp [b]; linarith
  have hb : b < 0 := by dsimp [b]; linarith
  have hab : a < b := hau.trans (huv.trans hvb)
  have hSt := Local.isSolution_mono h.solution (triangle_subset_origDomain hia hb)
  have hc := (Local.IsSolution.contDiffOn_r hSt hab).contDiffAt
    (mem_interior_iff_mem_nhds.mp (mem_interior_triangle_of_lt (p := (u, v)) hau huv hvb))
  let L := fderiv ℝ (Function.uncurry S.r) (u, v)
  have hfr : HasFDerivAt (Function.uncurry S.r) L (u, v) :=
    (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hsin : inSeg a v v ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff (hau.trans huv).le).2 ⟨hia, hv, le_rfl, hv.le⟩
  have hdU : HasDerivAt (fun x => S.r x v) (S.nu u v) u := by
    apply Local.hasDerivAt_of_integralForm_interior ⟨hau, huv⟩
      ((Calculus.continuousOn_in_section h.solution.cont_nu hsin).mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    exact (h.solution.eq_in c d v hcd hd
      (fun _ hp => hsin (inSeg_subset_inSeg hc.le hd.le hp))).1
  have hsout : outSeg u u b ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff (huv.trans hvb).le).2
      ⟨hui.le, huv.trans hv, le_rfl, hb.le⟩
  have hdV := Local.IsSolution.hasDerivAt_radius_out h.solution hsout ⟨huv, hvb⟩
  have hU := hfr.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
  have hV := hfr.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
  change HasDerivAt (fun x => S.r x v) (L (1, 0)) u at hU
  change HasDerivAt (S.r u) (L (0, 1)) v at hV
  have hLu := hU.unique hdU
  have hLv := hV.unique hdV
  have hL : L = S.nu u v • ContinuousLinearMap.fst ℝ ℝ ℝ +
      S.lam u v • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    apply DFunLike.ext
    intro q
    rcases q with ⟨x, y⟩
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    have hq : (x, y) = x • ((1 : ℝ), 0) + y • ((0 : ℝ), 1) := by ext <;> simp
    have hh := congrArg L hq
    rw [map_add, map_smul, map_smul, hLu, hLv] at hh
    simpa only [smul_eq_mul, mul_comm] using hh
  rw [← hL]
  exact hfr

/-- [internal]
Differentiability of a Lipschitz radius profile pulls back almost
everywhere under the strictly decreasing C¹ terminal radius. The proof
uses the nonnegative Jacobian formula on proper open intervals; no
pointwise derivative is restricted to an arbitrary curve. -/
theorem ae_differentiable_profile_at_radius {R nt ell : ℝ → ℝ} {a b R₀ : ℝ} {k : ℝ≥0}
    (_hab : a ≤ b) (cR : ContinuousOn R (Icc a b)) (cnt : ContinuousOn nt (Icc a b))
    (hdR : ∀ x ∈ Ioo a b, HasDerivAt R (nt x) x)
    (hnt : ∀ x ∈ Icc a b, nt x < 0)
    (hRange : ∀ x ∈ Icc a b, R x ∈ Ioo 0 R₀)
    (hLip : LipschitzOnWith k ell (Ioc 0 R₀)) :
    ∀ᵐ x ∂volume.restrict (Icc a b), DifferentiableAt ℝ ell (R x) := by
  have hdiff : ∀ᵐ ρ : ℝ, ρ ∈ Ioo 0 R₀ → DifferentiableAt ℝ ell ρ := by
    filter_upwards [hLip.ae_differentiableWithinAt_of_mem] with ρ hρ hmem
    exact (hρ ⟨hmem.1, hmem.2.le⟩).differentiableAt
      (mem_of_superset (Ioo_mem_nhds hmem.1 hmem.2) Ioo_subset_Ioc_self)
  have hbad0 : volume {ρ : ℝ | ρ ∈ Ioo 0 R₀ ∧ ¬DifferentiableAt ℝ ell ρ} = 0 := by
    have hh : ∀ᵐ ρ : ℝ, ¬(ρ ∈ Ioo 0 R₀ ∧ ¬DifferentiableAt ℝ ell ρ) :=
      hdiff.mono (fun ρ hρ => by tauto)
    simpa only [not_not] using (ae_iff.mp hh)
  obtain ⟨N, hsubN, hN, hN0⟩ := exists_measurable_superset_of_null hbad0
  let g := N.indicator (fun _ : ℝ => (1 : ℝ≥0∞))
  have hg : Measurable g := measurable_const.indicator hN
  have hAvoid : ∀ᵐ ρ : ℝ, ρ ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hg0 : g =ᵐ[volume] 0 := by
    filter_upwards [hAvoid] with ρ hρ
    simp [g, hρ]
  have hanti : StrictAntiOn R (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) cR
    intro x hx
    rw [interior_Icc] at hx
    rw [(hdR x hx).deriv]
    exact hnt x ⟨hx.1.le, hx.2.le⟩
  have hJac := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Ioo
    (fun x hx => (hdR x hx).hasDerivWithinAt) (hanti.antitoneOn.mono Ioo_subset_Icc_self) g
  have hzero : (∫⁻ x in Ioo a b, ENNReal.ofReal (-nt x) * g (R x)) = 0 := by
    rw [← hJac]
    rw [lintegral_congr_ae (ae_restrict_of_ae hg0)]
    simp only [Pi.zero_apply, lintegral_zero]
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (-nt x) * g (R x))
      (volume.restrict (Ioo a b)) :=
    (((ENNReal.continuous_ofReal.comp_continuousOn cnt.neg).mono Ioo_subset_Icc_self).aemeasurable
      measurableSet_Ioo).mul (hg.comp_aemeasurable
        ((cR.mono Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo))
  have hae := (lintegral_eq_zero_iff' hmeas).mp hzero
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hp : ENNReal.ofReal (-nt x) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (neg_pos.mpr (hnt x ⟨hmem.1.le, hmem.2.le⟩)))
  have hgzero := (mul_eq_zero.mp hx).resolve_left hp
  have hnmem : R x ∉ N := by
    intro hRx
    have hg1 : g (R x) = 1 := by simp [g, hRx]
    rw [hg1] at hgzero
    exact one_ne_zero hgzero
  by_contra hnot
  exact hnmem (hsubN ⟨hRange x ⟨hmem.1.le, hmem.2.le⟩, hnot⟩)

/-- [internal]
The literal almost-everywhere speed identity and its positive lower
bound on a proper frontier interval. The graph and profile are used with
their actual derivatives. The factor `1/2-k` is numerical, uniformly in
all original data; the Lipschitz graph constant is a proper-interval input
supplied by the frontier geometry consumer. -/
theorem frontier_speed_ae_of_graph {u₀ a b R₀ k : ℝ} {L : ℝ≥0}
    (h : OriginalData ui e S) (ell V : ℝ → ℝ) (hu₀ : u₀ ∈ Ioo ui 0)
    (hia : u₀ ≤ a) (hab : a ≤ b) (hb : b < 0) (hk : 0 ≤ k) (hkhalf : k < 1 / 2)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hV : LipschitzOnWith L V (Icc a b))
    (hRange : ∀ u ∈ Icc a b, S.r u 0 ∈ Ioo 0 R₀)
    (hroot : ∀ u ∈ Ico u₀ 0, u < V u ∧ V u < 0 ∧ S.r u (V u) = ell (S.r u 0))
    (hratio : ∀ u ∈ Ico u₀ 0, 1 / 2 < S.nu u (V u) / S.nu u 0) :
    ∀ᵐ u ∂volume.restrict (Icc a b),
      S.lam u (V u) * deriv V u =
          -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) ∧
        (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u ∧
        0 < S.lam u (V u) * deriv V u := by
  have hs0 : inSeg a b 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hab).2 ⟨hu₀.1.le.trans hia, hb, hb.le, le_rfl⟩
  have hdR (u : ℝ) (hu : u ∈ Ioo a b) := terminal_radius_hasDerivAt h
    (show u ∈ Ioo ui 0 from ⟨hu₀.1.trans_le (hia.trans hu.1.le), hu.2.trans hb⟩)
  have hprofile := ae_differentiable_profile_at_radius hab
    (Calculus.continuousOn_in_section h.solution.cont_r hs0)
    (Calculus.continuousOn_in_section h.solution.cont_nu hs0) hdR
    (fun u hu => h.solution.nu_neg (u, 0) (hs0 ⟨hu.1, hu.2, rfl⟩)) hRange hLip
  rw [← restrict_Ioo_eq_restrict_Icc] at hprofile ⊢
  filter_upwards [hprofile, ae_restrict_of_ae hV.ae_differentiableWithinAt_of_mem,
    ae_restrict_mem measurableSet_Ioo] with u hEll hVu hu
  have hu' : u ∈ Icc a b := ⟨hu.1.le, hu.2.le⟩
  have huLate : u ∈ Ico u₀ 0 := ⟨hia.trans hu.1.le, hu.2.trans hb⟩
  have hr := hroot u huLate
  have hdV := ((hVu hu').differentiableAt (Icc_mem_nhds hu.1 hu.2)).hasDerivAt
  have hdEll := hEll.hasDerivAt
  have hdRadius := radius_hasFDerivAt_of_interior h
    (hu₀.1.trans_le huLate.1) hr.1 hr.2.1
  have hcurve := hdRadius.comp_hasDerivAt u ((hasDerivAt_id u).prodMk hdV)
  change HasDerivAt (fun x => S.r x (V x))
    ((S.nu u (V u) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      S.lam u (V u) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, deriv V u)) u at hcurve
  have heq : (fun x => S.r x (V x)) =ᶠ[𝓝 u] (fun x => ell (S.r x 0)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    exact (hroot x ⟨hia.trans hx.1.le, hx.2.trans hb⟩).2.2
  have hchain := (hcurve.congr_of_eventuallyEq heq.symm).unique (hdEll.comp u (hdR u hu))
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one] at hchain
  have hidentity : S.lam u (V u) * deriv V u =
      -S.nu u (V u) - deriv ell (S.r u 0) * (-S.nu u 0) := by
    nlinarith only [hchain]
  have hdom : Ioc 0 R₀ ∈ 𝓝 (S.r u 0) :=
    mem_of_superset (Ioo_mem_nhds (hRange u hu').1 (hRange u hu').2) Ioo_subset_Ioc_self
  have hnorm := hdEll.le_of_lipschitzOn hdom hLip
  rw [Real.norm_eq_abs, Real.coe_toNNReal _ hk] at hnorm
  have hderiv := (le_abs_self (deriv ell (S.r u 0))).trans hnorm
  have hnt : S.nu u 0 < 0 := h.solution.nu_neg (u, 0) (hs0 ⟨hu'.1, hu'.2, rfl⟩)
  have hn := (lt_div_iff_of_neg hnt).mp (hratio u huLate)
  have hprod := mul_nonneg (sub_nonneg.mpr hderiv) (neg_nonneg.mpr hnt.le)
  have hlow : (1 / 2 - k) * (-S.nu u 0) ≤ S.lam u (V u) * deriv V u := by
    nlinarith only [hidentity, hn, hprod]
  exact ⟨hidentity, hlow, (mul_pos (sub_pos.mpr hkhalf) (neg_pos.mpr hnt)).trans_le hlow⟩

end EmcsfAcExtension.Global.Exterior
