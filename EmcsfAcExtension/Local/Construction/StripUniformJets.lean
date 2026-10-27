module

public import EmcsfAcExtension.Local.Construction.StripJetComparison
public import EmcsfAcExtension.Local.Construction.StripJetParameters
public import EmcsfAcExtension.Local.Construction.StripStateBounds
import EmcsfAcExtension.Local.Construction.StripCharacteristic

/-! # Uniform first jets and matching on the old lower edge

The fixed entering datum and state tube determine the height and value
tolerances before the old apex and both solutions are selected.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

open Broad

/-- Restriction to a nontrivial closed subinterval preserves the
canonical first derivative of a differentiable entering datum. -/
theorem derivWithin_Icc_eq_of_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b c d x : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ Icc c d)
    (hf : DifferentiableOn ℝ f (Icc c d)) (hx : x ∈ Icc a b) :
    derivWithin f (Icc a b) x = derivWithin f (Icc c d) x := by
  exact ((hf x (hsub hx)).hasDerivWithinAt.mono hsub).derivWithin
    (uniqueDiffOn_Icc hab x hx)

/-- The full derivative bound controls either canonical rectangle jet
with coefficient one in the maximum norm of the label plane. -/
theorem rectangle_jet_norm_le_of_fderiv_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b c d B : ℝ}
    {F : ℝ × ℝ → E} {p : ℝ × ℝ}
    (hB : ‖fderivWithin ℝ F (Icc a b ×ˢ Icc c d) p‖ ≤ B) :
    ‖rectangleJetU a b c d F p‖ ≤ B ∧ ‖rectangleJetV a b c d F p‖ ≤ B := by
  constructor
  · exact (ContinuousLinearMap.le_opNorm _ (1,0)).trans (by simpa [Prod.norm_def] using hB)
  · exact (ContinuousLinearMap.le_opNorm _ (0,1)).trans (by simpa [Prod.norm_def] using hB)

/-- The characteristic components of the canonical rectangle jets
are the actual sources, including every side and corner. -/
theorem goursat_characteristic_jet_eq (e : ℝ) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) {F : ℝ × ℝ → RectangleState}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hregion : MapsTo F (Icc a b ×ˢ Icc c d) rectangle_state_region)
    {yi : ℝ → RectangleIncoming} {xb : ℝ → RectangleOutgoing}
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, rectangle_in_source e (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, rectangle_out_source e (F (u, t)))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    (rectangleJetU a b c d F (u,v)).1 = rectangle_in_source e (F (u,v)) ∧
    (rectangleJetV a b c d F (u,v)).2 = rectangle_out_source e (F (u,v)) := by
  have hi : ContinuousOn (rectangle_in_source e) (F '' (Icc a b ×ˢ Icc c d)) := by
    rintro z ⟨p,hp,rfl⟩
    exact (contDiffAt_rectangle_in_source_two e (hregion hp)).continuousAt.continuousWithinAt
  have ho : ContinuousOn (rectangle_out_source e) (F '' (Icc a b ×ˢ Icc c d)) := by
    rintro z ⟨p,hp,rfl⟩
    exact (contDiffAt_rectangle_out_source_two e (hregion hp)).continuousAt.continuousWithinAt
  have hc := goursat_characteristic_hasDerivWithinAt hF.continuousOn hi ho hYi hXb hu hv
  constructor
  · have hj : HasDerivWithinAt (fun x => (F (x,v)).1)
        (rectangleJetU a b c d F (u,v)).1 (Icc a b) u :=
      (ContinuousLinearMap.fst ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt u
        (hasDerivWithinAt_rectangleJetU hF hu hv)
    exact (hj.derivWithin (uniqueDiffOn_Icc hab u hu)).symm.trans
      (hc.1.derivWithin (uniqueDiffOn_Icc hab u hu))
  · have hj : HasDerivWithinAt (fun x => (F (u,x)).2)
        (rectangleJetV a b c d F (u,v)).2 (Icc c d) v :=
      (ContinuousLinearMap.snd ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt v
        (hasDerivWithinAt_rectangleJetV hF hu hv)
    exact (hj.derivWithin (uniqueDiffOn_Icc hcd v hv)).symm.trans
      (hc.2.derivWithin (uniqueDiffOn_Icc hcd v hv))

/-- A fixed compact convex tube supplies one Lipschitz constant for
both literal sources, chosen before any solution or trace. -/
theorem rectangle_sources_lipschitz_on_tube (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region) :
    ∃ J > 0, ∀ x ∈ K, ∀ y ∈ K,
      ‖rectangle_in_source e x-rectangle_in_source e y‖ ≤ J*‖x-y‖ ∧
      ‖rectangle_out_source e x-rectangle_out_source e y‖ ≤ J*‖x-y‖ := by
  obtain ⟨J,hJ,hsize,_⟩ := rectangle_source_derivative_bounds e hK hconv hregion
  refine ⟨J,hJ,?_⟩
  intro x hx y hy
  exact ⟨hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (contDiffAt_rectangle_in_source_two e (hregion hz)).differentiableAt (by decide))
    (fun z hz => (hsize z hz).1) hy hx,
    hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (contDiffAt_rectangle_out_source_two e (hregion hz)).differentiableAt (by decide))
    (fun z hz => (hsize z hz).2) hy hx⟩

/-- Uniform first-jet recovery with an arbitrary fixed derivative
tolerance. The value tolerance and height are chosen before the old
apex, old band, and both states. Consequently `B` stays fixed throughout
the construction. The only datum modulus is that of the fixed `yi'`.
No second derivative of either solution or entering trace is used. -/
theorem exists_uniform_goursat_jet_bounds (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region)
    {T B q : ℝ} (hT : 0 < T) (hB : 0 < B) (hq : 0 < q)
    {yi : ℝ → RectangleIncoming} (hyi : ContDiffOn ℝ 1 yi (Icc 0 T)) :
    ∃ ζ > 0, ∃ δ₀ > 0,
    ∀ {l S h d : ℝ}, 0 ≤ l → l < S → S < h → h ≤ T →
      0 < d → d < S → h-S ≤ δ₀ →
    ∀ {W F : ℝ × ℝ → RectangleState} {xb₀ : ℝ → RectangleOutgoing},
      ContDiffOn ℝ 1 W (Icc 0 d ×ˢ Icc l S) →
      ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S h) →
      MapsTo W (Icc 0 d ×ˢ Icc l S) K → MapsTo F (Icc 0 d ×ˢ Icc S h) K →
      ContDiffOn ℝ 1 xb₀ (Icc 0 d) →
      (∀ u ∈ Icc 0 d, ∀ v ∈ Icc l S,
        (W (u,v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (W (s,v))) →
      (∀ u ∈ Icc 0 d, ∀ v ∈ Icc l S,
        (W (u,v)).2 = xb₀ u + ∫ t in l..v, rectangle_out_source e (W (u,t))) →
      (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S h,
        (F (u,v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (F (s,v))) →
      (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S h,
        (F (u,v)).2 = (W (u,S)).2 + ∫ t in S..v, rectangle_out_source e (F (u,t))) →
      (∀ p ∈ Icc 0 d ×ˢ Icc l S, ‖fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) p‖ ≤ B) →
      (∀ p ∈ Icc 0 d ×ˢ Icc S h, ‖F p-W (p.1,S)‖ ≤ ζ) →
      (∀ p ∈ Icc 0 d ×ˢ Icc S h,
        ‖fderivWithin ℝ F (Icc 0 d ×ˢ Icc S h) p-
          fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) (p.1,S)‖ ≤ q ∧
        ‖rectangleJetU 0 d S h F p‖ ≤ 2*B ∧
        ‖rectangleJetV 0 d S h F p‖ ≤ 2*B ∧
        ‖fderivWithin ℝ F (Icc 0 d ×ˢ Icc S h) p‖ ≤ 4*B) := by
  obtain ⟨C,hC,H,hH,hsize,hdiff⟩ := rectangle_jet_coefficient_bounds e hK hconv hregion
  obtain ⟨J,hJ,hsource⟩ := rectangle_sources_lipschitz_on_tube e hK hconv hregion
  let r := min B (q/2)
  have hr : 0 < r := lt_min hB (half_pos hq)
  have hrB : r ≤ B := min_le_left _ _
  have hrq : 2*r ≤ q := by
    have hh : r ≤ q/2 := min_le_right _ _
    linarith
  obtain ⟨ζ,hζ,δ₀,hδ₀,ω,hω,hJζ,hVsmall,hUsmall,hmod⟩ :=
    exists_uniform_jet_parameters hT hB hC hH hJ hr hyi
  refine ⟨ζ,hζ,δ₀,hδ₀,?_⟩
  intro l S h d hl0 hlS hSh hhT hd hdS hheight W F xb₀ hW hF hWK hFK hxb₀ hYiW hXbW hYiF hXbF hWB
      hclose
  have hS0 : 0 ≤ S := hl0.trans hlS.le
  have hdT : d ≤ T := hdS.le.trans (hSh.le.trans hhT)
  have hsubW : Icc l S ⊆ Icc 0 T := fun v hv => ⟨hl0.trans hv.1,hv.2.trans (hSh.le.trans hhT)⟩
  have hsubF : Icc S h ⊆ Icc 0 T := fun v hv => ⟨hS0.trans hv.1,hv.2.trans hhT⟩
  have hyiW := hyi.mono hsubW
  have hyiF := hyi.mono hsubF
  have hS : S ∈ Icc l S := ⟨hlS.le,le_rfl⟩
  have hWr : MapsTo W (Icc 0 d ×ˢ Icc l S) rectangle_state_region := fun p hp => hregion (hWK hp)
  have hFr : MapsTo F (Icc 0 d ×ˢ Icc S h) rectangle_state_region := fun p hp => hregion (hFK hp)
  have hxb : ContDiffOn ℝ 1 (fun u => (W (u,S)).2) (Icc 0 d) :=
    hW.snd.comp (contDiffOn_id.prodMk contDiffOn_const) (fun u hu => ⟨hu,hS⟩)
  have hxbprime u (hu : u ∈ Icc 0 d) :
      derivWithin (fun s => (W (s,S)).2) (Icc 0 d) u = (rectangleJetU 0 d l S W (u,S)).2 := by
    have hj : HasDerivWithinAt (fun s => (W (s,S)).2)
        (rectangleJetU 0 d l S W (u,S)).2 (Icc 0 d) u :=
      (ContinuousLinearMap.snd ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt u
        (hasDerivWithinAt_rectangleJetU hW hu hS)
    exact hj.derivWithin (uniqueDiffOn_Icc hd u hu)
  have hJU u (hu : u ∈ Icc 0 d) :=
    (rectangle_jet_norm_le_of_fderiv_bound (hWB (u,S) ⟨hu,hS⟩)).1
  have hJV u (hu : u ∈ Icc 0 d) :=
    (rectangle_jet_norm_le_of_fderiv_bound (hWB (u,S) ⟨hu,hS⟩)).2
  have hAf (u : ℝ) (hu : u ∈ Icc 0 d) (v : ℝ) (hv : v ∈ Icc S h) :=
    goursat_affine_transverse_jet_integral_eq e hd hSh hF hFr hyiF hxb hYiF hXbF hu hv
  have hAw (u : ℝ) (hu : u ∈ Icc 0 d) :=
    goursat_affine_transverse_jet_integral_eq e hd hlS hW hWr hyiW hxb₀ hYiW hXbW hu hS
  have hcf (u : ℝ) (hu : u ∈ Icc 0 d) (v : ℝ) (hv : v ∈ Icc S h) :=
    goursat_characteristic_jet_eq e hd hSh hF hFr hYiF hXbF hu hv
  have hcw (u : ℝ) (hu : u ∈ Icc 0 d) :=
    goursat_characteristic_jet_eq e hd hlS hW hWr hYiW hXbW hu hS
  rintro ⟨u,v⟩ ⟨hu,hv⟩
  have hfK : F (u,v) ∈ K := hFK ⟨hu,hv⟩
  have hwK : W (u,S) ∈ K := hWK ⟨hu,hS⟩
  have hclosev := fun s hs => hclose (s,v) ⟨hs,hv⟩
  have hinit : ‖derivWithin yi (Icc S h) v-derivWithin yi (Icc l S) S‖ ≤ ω := by
    rw [derivWithin_Icc_eq_of_subset hSh hsubF (hyi.differentiableOn (by decide)) hv,
      derivWithin_Icc_eq_of_subset hlS hsubW (hyi.differentiableOn (by decide)) hS]
    apply hmod v (hsubF hv) S (hsubW hS)
    rw [abs_of_nonneg (sub_nonneg.mpr hv.1)]
    exact (sub_le_sub_right hv.2 S).trans hheight
  have hV := transverse_jetV_difference_bound e hregion hd hlS hSh hv hC hH hB.le hζ.le hω.le
    hF hW hFK hWK (fun z hz => (hsize z hz).1)
    (fun x hx y hy => (hdiff x hx y hy).1)
    (fun x hx y hy => (hdiff x hx y hy).2.2.1)
    hclosev hJV hinit (fun s hs => (hAf s hs v hv).2) (fun s hs => (hAw s hs).2) u hu
  have hU := transverse_jetU_difference_bound e hregion hd hSh hu hC hH hB.le hF hFK
    (fun z hz => (hsize z hz).2.1) (fun z hz => (hsize z hz).2.2.2)
    ((norm_snd_le _).trans (hJU u hu)) (fun t ht =>
        by rw [← hxbprime u hu]; exact (hAf u hu t ht).1) v hv
  have hVle : ‖(rectangleJetV 0 d S h F (u,v)).1-(rectangleJetV 0 d l S W (u,S)).1‖ ≤ r := by
    apply hV.trans
    apply le_trans _ hVsmall
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl ω)
        (mul_le_mul_of_nonneg_left hdT (by positivity : 0 ≤ C*ζ*(B+H+C)))) (by norm_num))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hu.2.trans hdT) (by positivity)))
      (Real.exp_pos _).le (by positivity)
  have hUle : ‖(rectangleJetU 0 d S h F (u,v)).2-(rectangleJetU 0 d l S W (u,S)).2‖ ≤ r := by
    apply hU.trans
    apply le_trans _ hUsmall
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hheight (by positivity : 0 ≤ 2*C*(B+H)))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hv.2] : v-S ≤ T)
          (by positivity)))
      (Real.exp_pos _).le (by positivity)
  have hYu : ‖(rectangleJetU 0 d S h F (u,v)).1-(rectangleJetU 0 d l S W (u,S)).1‖ ≤ r := by
    rw [(hcf u hu v hv).1,(hcw u hu).1]
    exact ((hsource _ hfK _ hwK).1.trans
      (mul_le_mul_of_nonneg_left (hclosev u hu) hJ.le)).trans hJζ
  have hXv : ‖(rectangleJetV 0 d S h F (u,v)).2-(rectangleJetV 0 d l S W (u,S)).2‖ ≤ r := by
    rw [(hcf u hu v hv).2,(hcw u hu).2]
    exact ((hsource _ hfK _ hwK).2.trans
      (mul_le_mul_of_nonneg_left (hclosev u hu) hJ.le)).trans hJζ
  have hUd : ‖rectangleJetU 0 d S h F (u,v)-rectangleJetU 0 d l S W (u,S)‖ ≤ r :=
    max_le hYu hUle
  have hVd : ‖rectangleJetV 0 d S h F (u,v)-rectangleJetV 0 d l S W (u,S)‖ ≤ r :=
    max_le hVle hXv
  have hUn : ‖rectangleJetU 0 d S h F (u,v)‖ ≤ 2*B := by
    have hh := (norm_add_le (rectangleJetU 0 d S h F (u,v)-rectangleJetU 0 d l S W (u,S))
      (rectangleJetU 0 d l S W (u,S))).trans (add_le_add hUd (hJU u hu))
    rw [sub_add_cancel] at hh
    exact hh.trans (by linarith)
  have hVn : ‖rectangleJetV 0 d S h F (u,v)‖ ≤ 2*B := by
    have hh := (norm_add_le (rectangleJetV 0 d S h F (u,v)-rectangleJetV 0 d l S W (u,S))
      (rectangleJetV 0 d l S W (u,S))).trans (add_le_add hVd (hJV u hu))
    rw [sub_add_cancel] at hh
    exact hh.trans (by linarith)
  refine ⟨?_,hUn,hVn,?_⟩
  · have hh := norm_clm_le_two_mul_of_basis_bounds
      (fderivWithin ℝ F (Icc 0 d ×ˢ Icc S h) (u,v)-fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) (u,S))
      hr.le hUd hVd
    exact hh.trans hrq
  · exact (norm_clm_le_two_mul_of_basis_bounds _ (by positivity) hUn hVn).trans_eq (by ring)

/-- Exact equality of the full first derivative on the old/new seam.
The transverse incoming jet is identified by its actual linear Volterra
equation with zero initial and coefficient differences. Only an old
first-jet bound is used; no old second derivative is involved. -/
theorem goursat_seam_fderiv_eq (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region)
    {l S h d B : ℝ} (hd : 0 < d) (hlS : l < S) (hSh : S < h) (hB : 0 ≤ B)
    {W F : ℝ × ℝ → RectangleState} {yi : ℝ → RectangleIncoming} {xb₀ : ℝ → RectangleOutgoing}
    (hyi : ContDiffOn ℝ 1 yi (Icc l h))
    (hW : ContDiffOn ℝ 1 W (Icc 0 d ×ˢ Icc l S))
    (hF : ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S h))
    (hWK : MapsTo W (Icc 0 d ×ˢ Icc l S) K) (hFK : MapsTo F (Icc 0 d ×ˢ Icc S h) K)
    (hxb₀ : ContDiffOn ℝ 1 xb₀ (Icc 0 d))
    (hYiW : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc l S,
      (W (u, v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (W (s, v)))
    (hXbW : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc l S,
      (W (u, v)).2 = xb₀ u + ∫ t in l..v, rectangle_out_source e (W (u, t)))
    (hYiF : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S h,
      (F (u, v)).1 = yi v + ∫ s in 0..u, rectangle_in_source e (F (s, v)))
    (hXbF : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S h,
      (F (u, v)).2 = (W (u, S)).2 + ∫ t in S..v, rectangle_out_source e (F (u, t)))
    (hWB : ∀ p ∈ Icc 0 d ×ˢ Icc l S, ‖fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) p‖ ≤ B)
    (hseam : ∀ u ∈ Icc 0 d, F (u, S) = W (u, S)) :
    ∀ u ∈ Icc 0 d, fderivWithin ℝ F (Icc 0 d ×ˢ Icc S h) (u,S) =
      fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) (u,S) := by
  obtain ⟨C,hC,H,hH,hsize,hdiff⟩ := rectangle_jet_coefficient_bounds e hK hconv hregion
  have hS₀ : S ∈ Icc l S := ⟨hlS.le,le_rfl⟩
  have hS₁ : S ∈ Icc S h := ⟨le_rfl,hSh.le⟩
  have hsubW : Icc l S ⊆ Icc l h := Icc_subset_Icc le_rfl hSh.le
  have hsubF : Icc S h ⊆ Icc l h := Icc_subset_Icc hlS.le le_rfl
  have hyiW := hyi.mono hsubW
  have hyiF := hyi.mono hsubF
  have hWr : MapsTo W (Icc 0 d ×ˢ Icc l S) rectangle_state_region := fun p hp => hregion (hWK hp)
  have hFr : MapsTo F (Icc 0 d ×ˢ Icc S h) rectangle_state_region := fun p hp => hregion (hFK hp)
  have hxb : ContDiffOn ℝ 1 (fun u => (W (u,S)).2) (Icc 0 d) :=
    hW.snd.comp (contDiffOn_id.prodMk contDiffOn_const) (fun u hu => ⟨hu,hS₀⟩)
  have hAf (u : ℝ) (hu : u ∈ Icc 0 d) :=
    goursat_affine_transverse_jet_integral_eq e hd hSh hF hFr hyiF hxb hYiF hXbF hu hS₁
  have hAw (u : ℝ) (hu : u ∈ Icc 0 d) :=
    goursat_affine_transverse_jet_integral_eq e hd hlS hW hWr hyiW hxb₀ hYiW hXbW hu hS₀
  have hinit : ‖derivWithin yi (Icc S h) S-derivWithin yi (Icc l S) S‖ ≤ (0 : ℝ) := by
    rw [derivWithin_Icc_eq_of_subset hSh hsubF (hyi.differentiableOn (by decide)) hS₁,
      derivWithin_Icc_eq_of_subset hlS hsubW (hyi.differentiableOn (by decide)) hS₀]
    simp
  have hV := transverse_jetV_difference_bound e hregion hd hlS hSh hS₁ hC hH hB
    (le_refl 0) (le_refl 0) hF hW hFK hWK (fun z hz => (hsize z hz).1)
    (fun x hx y hy => (hdiff x hx y hy).1)
    (fun x hx y hy => (hdiff x hx y hy).2.2.1)
    (fun u hu => by rw [hseam u hu]; simp)
    (fun u hu => (rectangle_jet_norm_le_of_fderiv_bound (hWB (u,S) ⟨hu,hS₀⟩)).2)
    hinit (fun u hu => (hAf u hu).2) (fun u hu => (hAw u hu).2)
  intro u hu
  have hVfirst : (rectangleJetV 0 d S h F (u,S)).1 = (rectangleJetV 0 d l S W (u,S)).1 := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hV u hu) (norm_nonneg _)
  have hUsecond : (rectangleJetU 0 d S h F (u,S)).2 = (rectangleJetU 0 d l S W (u,S)).2 := by
    have hj : HasDerivWithinAt (fun s => (W (s,S)).2)
        (rectangleJetU 0 d l S W (u,S)).2 (Icc 0 d) u :=
      (ContinuousLinearMap.snd ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt u
        (hasDerivWithinAt_rectangleJetU hW hu hS₀)
    have hh : (rectangleJetU 0 d S h F (u,S)).2 =
        derivWithin (fun s => (W (s,S)).2) (Icc 0 d) u := by
      simpa using (hAf u hu).1
    exact hh.trans (hj.derivWithin (uniqueDiffOn_Icc hd u hu))
  have hcf := goursat_characteristic_jet_eq e hd hSh hF hFr hYiF hXbF hu hS₁
  have hcw := goursat_characteristic_jet_eq e hd hlS hW hWr hYiW hXbW hu hS₀
  have hUeq : rectangleJetU 0 d S h F (u,S) = rectangleJetU 0 d l S W (u,S) :=
    Prod.ext (by rw [hcf.1,hcw.1,hseam u hu]) hUsecond
  have hVeq : rectangleJetV 0 d S h F (u,S) = rectangleJetV 0 d l S W (u,S) :=
    Prod.ext hVfirst (by rw [hcf.2,hcw.2,hseam u hu])
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hh := norm_clm_le_two_mul_of_basis_bounds
    (fderivWithin ℝ F (Icc 0 d ×ˢ Icc S h) (u,S)-fderivWithin ℝ W (Icc 0 d ×ˢ Icc l S) (u,S))
    (le_refl (0 : ℝ))
    (show ‖rectangleJetU 0 d S h F (u,S)-rectangleJetU 0 d l S W (u,S)‖ ≤ 0 from by rw [hUeq]; simp)
    (show ‖rectangleJetV 0 d S h F (u,S)-rectangleJetV 0 d l S W (u,S)‖ ≤ 0 from by rw [hVeq]; simp)
  simpa using hh

end EmcsfAcExtension.Local
