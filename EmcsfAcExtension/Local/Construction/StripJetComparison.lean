module

public import EmcsfAcExtension.Local.Construction.StripJetCoefficients
public import EmcsfAcExtension.Local.Construction.StripJetBounds

/-! # Comparing the actual transverse jets

These estimates apply the affine Volterra comparison to canonical first
jets. Only old first-jet bounds and state differences enter.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

open Broad

/-- Pointwise outgoing-transverse incoming-jet comparison. The affine
identities are supplied by `goursat_affine_transverse_jet_integral_eq`.
`C,H` are fixed state-tube constants, independent of both states. -/
theorem transverse_jetV_difference_bound (e : ℝ) {K : Set RectangleState}
    (hregion : K ⊆ rectangle_state_region) {d l S v h C H B ζ ω : ℝ}
    (hd : 0 < d) (hlS : l < S) (hSh : S < h)
    (hv : v ∈ Icc S h) (hC : 0 < C) (hH : 0 < H)
    (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hω : 0 ≤ ω)
    {F W : ℝ × ℝ → RectangleState}
    (hF : ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S h))
    (hW : ContDiffOn ℝ 1 W (Icc 0 d ×ˢ Icc l S))
    (hFK : MapsTo F (Icc 0 d ×ˢ Icc S h) K)
    (hWK : MapsTo W (Icc 0 d ×ˢ Icc l S) K)
    (hAi : ∀ z ∈ K, ‖rectangle_in_jet_coefficient e z‖ ≤ C)
    (hAid : ∀ x ∈ K, ∀ y ∈ K,
      ‖rectangle_in_jet_coefficient e x - rectangle_in_jet_coefficient e y‖ ≤ C * ‖x - y‖)
    (hbid : ∀ x ∈ K, ∀ y ∈ K,
      ‖rectangle_in_jet_forcing e x - rectangle_in_jet_forcing e y‖ ≤ C * (H + C) * ‖x - y‖)
    (hclose : ∀ u ∈ Icc 0 d, ‖F (u, v) - W (u, S)‖ ≤ ζ)
    (hWbound : ∀ u ∈ Icc 0 d, ‖rectangleJetV 0 d l S W (u, S)‖ ≤ B)
    {z z₀ : RectangleIncoming} (hinit : ‖z - z₀‖ ≤ ω)
    (heq : ∀ u ∈ Icc 0 d, (rectangleJetV 0 d S h F (u, v)).1 = z +
      ∫ s in 0..u, rectangle_in_jet_coefficient e (F (s, v))
        (rectangleJetV 0 d S h F (s, v)).1 + rectangle_in_jet_forcing e (F (s, v)))
    (heq₀ : ∀ u ∈ Icc 0 d, (rectangleJetV 0 d l S W (u, S)).1 = z₀ +
      ∫ s in 0..u, rectangle_in_jet_coefficient e (W (s, S))
        (rectangleJetV 0 d l S W (s, S)).1 + rectangle_in_jet_forcing e (W (s, S))) :
    ∀ u ∈ Icc 0 d,
      ‖(rectangleJetV 0 d S h F (u,v)).1-(rectangleJetV 0 d l S W (u,S)).1‖ ≤
        2*(ω+C*ζ*(B+H+C)*d)*Real.exp (2*(C+1)*u) := by
  have hS : S ∈ Icc l S := ⟨hlS.le,le_rfl⟩
  have hlineF : ContinuousOn (fun u : ℝ => (u,v)) (Icc 0 d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hlineW : ContinuousOn (fun u : ℝ => (u,S)) (Icc 0 d) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hc := continuousOn_rectangle_jet_coefficients e hregion
  have hAiF := hc.1.comp (hF.continuousOn.comp hlineF (fun u hu => ⟨hu,hv⟩))
    (fun u hu => hFK ⟨hu,hv⟩)
  have hAiW := hc.1.comp (hW.continuousOn.comp hlineW (fun u hu => ⟨hu,hS⟩))
    (fun u hu => hWK ⟨hu,hS⟩)
  have hbiF := hc.2.2.1.comp (hF.continuousOn.comp hlineF (fun u hu => ⟨hu,hv⟩))
    (fun u hu => hFK ⟨hu,hv⟩)
  have hbiW := hc.2.2.1.comp (hW.continuousOn.comp hlineW (fun u hu => ⟨hu,hS⟩))
    (fun u hu => hWK ⟨hu,hS⟩)
  have hw := (continuousOn_rectangleJetV hd hSh hF).fst.comp hlineF (fun u hu => ⟨hu,hv⟩)
  have hw₀ := (continuousOn_rectangleJetV hd hlS hW).fst.comp hlineW (fun u hu => ⟨hu,hS⟩)
  have hb := linear_volterra_difference_bound hd.le hC.le hB
    (mul_nonneg hC.le hζ) (by positivity : 0 ≤ C*(H+C)*ζ) hω
    hw hw₀ hAiF hAiW hbiF hbiW heq heq₀ hinit (by
      intro s hs
      have hf : F (s,v) ∈ K := hFK ⟨hs,hv⟩
      have hwk : W (s,S) ∈ K := hWK ⟨hs,hS⟩
      exact ⟨hAi _ hf, (norm_fst_le _).trans (hWbound s hs),
        (hAid _ hf _ hwk).trans (mul_le_mul_of_nonneg_left (hclose s hs) hC.le),
        (hbid _ hf _ hwk).trans (mul_le_mul_of_nonneg_left (hclose s hs) (by positivity))⟩)
  intro u hu
  have hb' := hb u hu
  dsimp only [Function.comp_apply] at hb'
  calc
    _ ≤ 2*(ω+(C*ζ*B+C*(H+C)*ζ)*(d-0))*Real.exp (2*(C+1)*(u-0)) := hb'
    _ = _ := by simp only [sub_zero]; ring

/-- The incoming-transverse outgoing jet differs from its lower-edge
value by a quantity tending to zero with strip height. The comparison
function is constant, so the exponential factor multiplies only the
small residual and never the old first-jet bound alone. -/
theorem transverse_jetU_difference_bound (e : ℝ) {K : Set RectangleState}
    (hregion : K ⊆ rectangle_state_region) {d S h u C H B : ℝ}
    (hd : 0 < d) (hSh : S < h) (hu : u ∈ Icc 0 d)
    (hC : 0 < C) (hH : 0 < H) (hB : 0 ≤ B)
    {F : ℝ × ℝ → RectangleState}
    (hF : ContDiffOn ℝ 1 F (Icc 0 d ×ˢ Icc S h))
    (hFK : MapsTo F (Icc 0 d ×ˢ Icc S h) K)
    (hAo : ∀ z ∈ K, ‖rectangle_out_jet_coefficient e z‖ ≤ C)
    (hbo : ∀ z ∈ K, ‖rectangle_out_jet_forcing e z‖ ≤ C * H)
    {z : RectangleOutgoing} (hz : ‖z‖ ≤ B)
    (heq : ∀ v ∈ Icc S h, (rectangleJetU 0 d S h F (u, v)).2 = z +
      ∫ t in S..v, rectangle_out_jet_coefficient e (F (u, t))
        (rectangleJetU 0 d S h F (u, t)).2 + rectangle_out_jet_forcing e (F (u, t))) :
    ∀ v ∈ Icc S h,
      ‖(rectangleJetU 0 d S h F (u,v)).2-z‖ ≤
        2*C*(B+H)*(h-S)*Real.exp (2*(C+1)*(v-S)) := by
  have hline : ContinuousOn (fun v : ℝ => (u,v)) (Icc S h) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hc := continuousOn_rectangle_jet_coefficients e hregion
  have hAF := hc.2.1.comp (hF.continuousOn.comp hline (fun v hv => ⟨hu,hv⟩))
    (fun v hv => hFK ⟨hu,hv⟩)
  have hbF := hc.2.2.2.comp (hF.continuousOn.comp hline (fun v hv => ⟨hu,hv⟩))
    (fun v hv => hFK ⟨hu,hv⟩)
  have hw := (continuousOn_rectangleJetU hd hSh hF).snd.comp hline (fun v hv => ⟨hu,hv⟩)
  have heq₀ : ∀ x ∈ Icc S h, z = z + ∫ s in S..x,
      (0 : RectangleOutgoing →L[ℝ] RectangleOutgoing) z+(0 : RectangleOutgoing) := by
    intro x hx
    simp
  have hb := linear_volterra_difference_bound hSh.le hC.le hB hC.le
    (mul_nonneg hC.le hH.le) (le_refl 0) hw continuousOn_const hAF continuousOn_const
    hbF continuousOn_const heq heq₀ (by simp : ‖z-z‖ ≤ (0 : ℝ)) (by
      intro s hs
      have hk : F (u,s) ∈ K := hFK ⟨hu,hs⟩
      simpa only [Function.comp_apply, sub_zero] using
        And.intro (hAo _ hk) (And.intro hz (And.intro (hAo _ hk) (hbo _ hk))))
  intro v hv
  have hb' := hb v hv
  dsimp only [Function.comp_apply] at hb'
  calc
    _ ≤ 2*(0+(C*B+C*H)*(h-S))*Real.exp (2*(C+1)*(v-S)) := hb'
    _ = _ := by ring

end EmcsfAcExtension.Local
