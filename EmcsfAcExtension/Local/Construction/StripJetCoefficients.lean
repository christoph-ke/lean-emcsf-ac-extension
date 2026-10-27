module

public import EmcsfAcExtension.Local.Construction.StripSources
public import EmcsfAcExtension.Local.Construction.StripJets
import EmcsfAcExtension.Local.Construction.StripCharacteristic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual affine coefficients of the transverse first-jet equations

The linear coefficients and forcing terms below are the literal first
state derivatives in internal project record (47). A fixed compact convex tube
supplies uniform size and difference constants before any old trace,
apex, or constructed state is selected.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- Linear coefficient of the incoming block's outgoing transverse jet. -/
@[expose] noncomputable def rectangle_in_jet_coefficient (e : ℝ) (z : RectangleState) :
    RectangleIncoming →L[ℝ] RectangleIncoming :=
  fderiv ℝ (rectangle_in_source e) z ∘L
    ContinuousLinearMap.inl ℝ RectangleIncoming RectangleOutgoing

/-- Forcing in the incoming block's outgoing transverse jet equation. -/
@[expose] noncomputable def rectangle_in_jet_forcing (e : ℝ) (z : RectangleState) :
    RectangleIncoming :=
  fderiv ℝ (rectangle_in_source e) z (0, rectangle_out_source e z)

/-- Linear coefficient of the outgoing block's incoming transverse jet. -/
@[expose] noncomputable def rectangle_out_jet_coefficient (e : ℝ) (z : RectangleState) :
    RectangleOutgoing →L[ℝ] RectangleOutgoing :=
  fderiv ℝ (rectangle_out_source e) z ∘L
    ContinuousLinearMap.inr ℝ RectangleIncoming RectangleOutgoing

/-- Forcing in the outgoing block's incoming transverse jet equation. -/
@[expose] noncomputable def rectangle_out_jet_forcing (e : ℝ) (z : RectangleState) :
    RectangleOutgoing :=
  fderiv ℝ (rectangle_out_source e) z (rectangle_in_source e z, 0)

/-- The incoming first-jet source splits into its linear unknown and
its known outgoing-characteristic forcing, with exact coefficients. -/
theorem rectangle_in_jet_decomposition (e : ℝ) (z : RectangleState) (y : RectangleIncoming) :
    rectangle_in_jet_coefficient e z y + rectangle_in_jet_forcing e z =
      fderiv ℝ (rectangle_in_source e) z (y, rectangle_out_source e z) := by
  change fderiv ℝ (rectangle_in_source e) z (y,0) +
    fderiv ℝ (rectangle_in_source e) z (0,rectangle_out_source e z) = _
  rw [← map_add]
  congr 1
  ext <;> simp

/-- The outgoing first-jet source has the analogous exact affine split. -/
theorem rectangle_out_jet_decomposition (e : ℝ) (z : RectangleState) (x : RectangleOutgoing) :
    rectangle_out_jet_coefficient e z x + rectangle_out_jet_forcing e z =
      fderiv ℝ (rectangle_out_source e) z (rectangle_in_source e z, x) := by
  change fderiv ℝ (rectangle_out_source e) z (0,x) +
    fderiv ℝ (rectangle_out_source e) z (rectangle_in_source e z,0) = _
  rw [← map_add]
  congr 1
  ext <;> simp

/-- The actual affine coefficients and forcing are continuous on every
state set contained in the nondegenerate region. Compactness and
convexity are needed only for the quantitative bounds below. -/
theorem continuousOn_rectangle_jet_coefficients (e : ℝ) {K : Set RectangleState}
    (hregion : K ⊆ rectangle_state_region) :
    ContinuousOn (rectangle_in_jet_coefficient e) K ∧
    ContinuousOn (rectangle_out_jet_coefficient e) K ∧
    ContinuousOn (rectangle_in_jet_forcing e) K ∧
    ContinuousOn (rectangle_out_jet_forcing e) K := by
  have hi : ContinuousOn (rectangle_in_source e) K := fun z hz =>
    (contDiffAt_rectangle_in_source_two e (hregion hz)).continuousAt.continuousWithinAt
  have ho : ContinuousOn (rectangle_out_source e) K := fun z hz =>
    (contDiffAt_rectangle_out_source_two e (hregion hz)).continuousAt.continuousWithinAt
  have hDi₁ : ContDiffOn ℝ 1 (fderiv ℝ (rectangle_in_source e)) K := fun z hz =>
    ((contDiffAt_rectangle_in_source_two e (hregion hz)).fderiv_right
      (by norm_num)).contDiffWithinAt
  have hDo₁ : ContDiffOn ℝ 1 (fderiv ℝ (rectangle_out_source e)) K := fun z hz =>
    ((contDiffAt_rectangle_out_source_two e (hregion hz)).fderiv_right
      (by norm_num)).contDiffWithinAt
  have hDi := hDi₁.continuousOn
  have hDo := hDo₁.continuousOn
  exact ⟨hDi.clm_comp continuousOn_const, hDo.clm_comp continuousOn_const,
    hDi.clm_apply (continuousOn_const.prodMk ho), hDo.clm_apply (hi.prodMk continuousOn_const)⟩

private theorem norm_precomp_inl_le {I O G : Type*}
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup O] [NormedSpace ℝ O]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : I × O →L[ℝ] G) :
    ‖A ∘L ContinuousLinearMap.inl ℝ I O‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖A (x,0)‖ ≤ ‖A‖ * ‖x‖
  simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)] using A.le_opNorm (x,0)

private theorem norm_precomp_inr_le {I O G : Type*}
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup O] [NormedSpace ℝ O]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (A : I × O →L[ℝ] G) :
    ‖A ∘L ContinuousLinearMap.inr ℝ I O‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  change ‖A (0,x)‖ ≤ ‖A‖ * ‖x‖
  simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg x)] using A.le_opNorm (0,x)

private theorem norm_apply_sub_apply_bound {I G : Type*}
    [NormedAddCommGroup I] [NormedSpace ℝ I] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A B : I →L[ℝ] G) (x y : I) :
    ‖A x-B y‖ ≤ ‖A-B‖*‖x‖ + ‖B‖*‖x-y‖ := by
  calc
    ‖A x-B y‖ ≤ ‖A x-B x‖ + ‖B x-B y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (A x) (B x) (B y)
    _ = ‖(A-B) x‖ + ‖B (x-y)‖ := by simp only [sub_apply, map_sub]
    _ ≤ ‖A-B‖*‖x‖ + ‖B‖*‖x-y‖ := add_le_add ((A-B).le_opNorm x) (B.le_opNorm (x-y))

/-- Uniform bounds for the actual affine first-jet coefficients on one
fixed compact convex nondegenerate tube. `C,H` depend only on `e,K` and
precede both states; they are uniform in all traces and old apex values.
The forcing difference uses the first-state-derivative Lipschitz bound,
with no second derivative or modulus of an old solution. -/
theorem rectangle_jet_coefficient_bounds (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region) :
    ∃ C > 0, ∃ H > 0,
      (∀ z ∈ K,
        ‖rectangle_in_jet_coefficient e z‖ ≤ C ∧
        ‖rectangle_out_jet_coefficient e z‖ ≤ C ∧
        ‖rectangle_in_jet_forcing e z‖ ≤ C*H ∧
        ‖rectangle_out_jet_forcing e z‖ ≤ C*H) ∧
      (∀ x ∈ K, ∀ y ∈ K,
        ‖rectangle_in_jet_coefficient e x-rectangle_in_jet_coefficient e y‖ ≤ C*‖x-y‖ ∧
        ‖rectangle_out_jet_coefficient e x-rectangle_out_jet_coefficient e y‖ ≤ C*‖x-y‖ ∧
        ‖rectangle_in_jet_forcing e x-rectangle_in_jet_forcing e y‖ ≤ C*(H+C)*‖x-y‖ ∧
        ‖rectangle_out_jet_forcing e x-rectangle_out_jet_forcing e y‖ ≤ C*(H+C)*‖x-y‖) := by
  obtain ⟨C,hC,hDs,hDd⟩ := rectangle_source_derivative_bounds e hK hconv hregion
  have hi : ContinuousOn (rectangle_in_source e) K := fun z hz =>
    (contDiffAt_rectangle_in_source_two e (hregion hz)).continuousAt.continuousWithinAt
  have ho : ContinuousOn (rectangle_out_source e) K := fun z hz =>
    (contDiffAt_rectangle_out_source_two e (hregion hz)).continuousAt.continuousWithinAt
  obtain ⟨Hi,hHi⟩ := hK.exists_bound_of_continuousOn hi
  obtain ⟨Ho,hHo⟩ := hK.exists_bound_of_continuousOn ho
  let H := 1+|Hi|+|Ho|
  have hH : 0 < H := by dsimp [H]; positivity
  have hHiH : Hi ≤ H := by dsimp [H]; linarith [le_abs_self Hi, abs_nonneg Ho]
  have hHoH : Ho ≤ H := by dsimp [H]; linarith [le_abs_self Ho, abs_nonneg Hi]
  have his z (hz : z ∈ K) : ‖rectangle_in_source e z‖ ≤ H := (hHi z hz).trans hHiH
  have hos z (hz : z ∈ K) : ‖rectangle_out_source e z‖ ≤ H := (hHo z hz).trans hHoH
  have hid x (hx : x ∈ K) y (hy : y ∈ K) :
      ‖rectangle_in_source e x-rectangle_in_source e y‖ ≤ C*‖x-y‖ :=
    hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (contDiffAt_rectangle_in_source_two e (hregion hz)).differentiableAt (by decide))
      (fun z hz => (hDs z hz).1) hy hx
  have hod x (hx : x ∈ K) y (hy : y ∈ K) :
      ‖rectangle_out_source e x-rectangle_out_source e y‖ ≤ C*‖x-y‖ :=
    hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => (contDiffAt_rectangle_out_source_two e (hregion hz)).differentiableAt
          (by decide))
      (fun z hz => (hDs z hz).2) hy hx
  have hAi z (hz : z ∈ K) : ‖rectangle_in_jet_coefficient e z‖ ≤ C :=
    (norm_precomp_inl_le _).trans (hDs z hz).1
  have hAo z (hz : z ∈ K) : ‖rectangle_out_jet_coefficient e z‖ ≤ C :=
    (norm_precomp_inr_le _).trans (hDs z hz).2
  have hBi z (hz : z ∈ K) :
      ‖fderiv ℝ (rectangle_in_source e) z ∘L
        ContinuousLinearMap.inr ℝ RectangleIncoming RectangleOutgoing‖ ≤ C :=
    (norm_precomp_inr_le _).trans (hDs z hz).1
  have hBo z (hz : z ∈ K) :
      ‖fderiv ℝ (rectangle_out_source e) z ∘L
        ContinuousLinearMap.inl ℝ RectangleIncoming RectangleOutgoing‖ ≤ C :=
    (norm_precomp_inl_le _).trans (hDs z hz).2
  refine ⟨C,hC,H,hH,?_,?_⟩
  · intro z hz
    refine ⟨hAi z hz,hAo z hz,?_,?_⟩
    · exact ((fderiv ℝ (rectangle_in_source e) z ∘L
        ContinuousLinearMap.inr ℝ RectangleIncoming RectangleOutgoing).le_opNorm
        (rectangle_out_source e z)).trans
        (mul_le_mul (hBi z hz) (hos z hz) (norm_nonneg _) hC.le)
    · exact ((fderiv ℝ (rectangle_out_source e) z ∘L
        ContinuousLinearMap.inl ℝ RectangleIncoming RectangleOutgoing).le_opNorm
        (rectangle_in_source e z)).trans
        (mul_le_mul (hBo z hz) (his z hz) (norm_nonneg _) hC.le)
  · intro x hx y hy
    have hAid : ‖rectangle_in_jet_coefficient e x-rectangle_in_jet_coefficient e y‖ ≤ C*‖x-y‖ := by
      unfold rectangle_in_jet_coefficient
      rw [← ContinuousLinearMap.sub_comp]
      exact (norm_precomp_inl_le _).trans (hDd x hx y hy).1
    have hAod : ‖rectangle_out_jet_coefficient e x-rectangle_out_jet_coefficient e y‖ ≤ C*‖x-y‖ :=
        by
      unfold rectangle_out_jet_coefficient
      rw [← ContinuousLinearMap.sub_comp]
      exact (norm_precomp_inr_le _).trans (hDd x hx y hy).2
    refine ⟨hAid,hAod,?_,?_⟩
    · have hBid : ‖(fderiv ℝ (rectangle_in_source e) x ∘L ContinuousLinearMap.inr ℝ
        RectangleIncoming RectangleOutgoing) -
          (fderiv ℝ (rectangle_in_source e) y ∘L ContinuousLinearMap.inr ℝ RectangleIncoming
              RectangleOutgoing)‖ ≤ C*‖x-y‖ := by
        rw [← ContinuousLinearMap.sub_comp]
        exact (norm_precomp_inr_le _).trans (hDd x hx y hy).1
      exact (norm_apply_sub_apply_bound
        (fderiv ℝ (rectangle_in_source e) x ∘L ContinuousLinearMap.inr ℝ RectangleIncoming
            RectangleOutgoing)
        (fderiv ℝ (rectangle_in_source e) y ∘L ContinuousLinearMap.inr ℝ RectangleIncoming
            RectangleOutgoing)
        (rectangle_out_source e x) (rectangle_out_source e y)).trans
        ((add_le_add
          (mul_le_mul hBid (hos x hx) (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _)))
          (mul_le_mul (hBi y hy) (hod x hx y hy) (norm_nonneg _) hC.le)).trans_eq (by ring))
    · have hBod : ‖(fderiv ℝ (rectangle_out_source e) x ∘L ContinuousLinearMap.inl ℝ
        RectangleIncoming RectangleOutgoing) -
          (fderiv ℝ (rectangle_out_source e) y ∘L ContinuousLinearMap.inl ℝ RectangleIncoming
              RectangleOutgoing)‖ ≤ C*‖x-y‖ := by
        rw [← ContinuousLinearMap.sub_comp]
        exact (norm_precomp_inl_le _).trans (hDd x hx y hy).2
      exact (norm_apply_sub_apply_bound
        (fderiv ℝ (rectangle_out_source e) x ∘L ContinuousLinearMap.inl ℝ RectangleIncoming
            RectangleOutgoing)
        (fderiv ℝ (rectangle_out_source e) y ∘L ContinuousLinearMap.inl ℝ RectangleIncoming
            RectangleOutgoing)
        (rectangle_in_source e x) (rectangle_in_source e y)).trans
        ((add_le_add
          (mul_le_mul hBod (his x hx) (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _)))
          (mul_le_mul (hBo y hy) (hid x hx y hy) (norm_nonneg _) hC.le)).trans_eq (by ring))

/-- The actual transverse jets solve affine Volterra equations with the
literal source coefficients defined above. Both identities hold on all
four rectangle sides. No transverse derivative is supplied as a premise:
the jets are the canonical derivatives of the C¹ state. -/
theorem goursat_affine_transverse_jet_integral_eq (e : ℝ) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) {F : ℝ × ℝ → RectangleState}
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hregion : MapsTo F (Icc a b ×ˢ Icc c d) rectangle_state_region)
    {yi : ℝ → RectangleIncoming} {xb : ℝ → RectangleOutgoing}
    (hyi : ContDiffOn ℝ 1 yi (Icc c d)) (hxb : ContDiffOn ℝ 1 xb (Icc a b))
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, rectangle_in_source e (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, rectangle_out_source e (F (u, t)))
    {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    ((rectangleJetU a b c d F (u,v)).2 = derivWithin xb (Icc a b) u +
      ∫ t in c..v, rectangle_out_jet_coefficient e (F (u,t))
        (rectangleJetU a b c d F (u,t)).2 + rectangle_out_jet_forcing e (F (u,t))) ∧
    ((rectangleJetV a b c d F (u,v)).1 = derivWithin yi (Icc c d) v +
      ∫ s in a..u, rectangle_in_jet_coefficient e (F (s,v))
        (rectangleJetV a b c d F (s,v)).1 + rectangle_in_jet_forcing e (F (s,v))) := by
  have hi p (hp : p ∈ Icc a b ×ˢ Icc c d) :
      ContDiffAt ℝ 1 (rectangle_in_source e) (F p) :=
    (contDiffAt_rectangle_in_source_two e (hregion hp)).of_le (by decide)
  have ho p (hp : p ∈ Icc a b ×ˢ Icc c d) :
      ContDiffAt ℝ 1 (rectangle_out_source e) (F p) :=
    (contDiffAt_rectangle_out_source_two e (hregion hp)).of_le (by decide)
  have hci : ContinuousOn (rectangle_in_source e) (F '' (Icc a b ×ˢ Icc c d)) := by
    rintro z ⟨p,hp,rfl⟩
    exact (hi p hp).continuousAt.continuousWithinAt
  have hco : ContinuousOn (rectangle_out_source e) (F '' (Icc a b ×ˢ Icc c d)) := by
    rintro z ⟨p,hp,rfl⟩
    exact (ho p hp).continuousAt.continuousWithinAt
  have hju s (hs : s ∈ Icc a b) t (ht : t ∈ Icc c d) :
      (rectangleJetU a b c d F (s,t)).1 = rectangle_in_source e (F (s,t)) := by
    have hj : HasDerivWithinAt (fun x => (F (x,t)).1)
        (rectangleJetU a b c d F (s,t)).1 (Icc a b) s :=
      (ContinuousLinearMap.fst ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt s
        (hasDerivWithinAt_rectangleJetU hF hs ht)
    exact (hj.derivWithin (uniqueDiffOn_Icc hab s hs)).symm.trans
      ((goursat_characteristic_hasDerivWithinAt hF.continuousOn hci hco hYi hXb hs ht).1.derivWithin
        (uniqueDiffOn_Icc hab s hs))
  have hjv s (hs : s ∈ Icc a b) t (ht : t ∈ Icc c d) :
      (rectangleJetV a b c d F (s,t)).2 = rectangle_out_source e (F (s,t)) := by
    have hj : HasDerivWithinAt (fun x => (F (s,x)).2)
        (rectangleJetV a b c d F (s,t)).2 (Icc c d) t :=
      (ContinuousLinearMap.snd ℝ RectangleIncoming
          RectangleOutgoing).hasFDerivAt.comp_hasDerivWithinAt t
        (hasDerivWithinAt_rectangleJetV hF hs ht)
    exact (hj.derivWithin (uniqueDiffOn_Icc hcd t ht)).symm.trans
      ((goursat_characteristic_hasDerivWithinAt hF.continuousOn hci hco hYi hXb hs ht).2.derivWithin
        (uniqueDiffOn_Icc hcd t ht))
  constructor
  · rw [goursat_transverse_jetU_integral_eq hab hcd hF hxb ho hXb hu hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    dsimp only
    rw [rectangle_out_jet_decomposition, ← hju u hu t ⟨ht.1,ht.2.trans hv.2⟩]
  · rw [goursat_transverse_jetV_integral_eq hab hcd hF hyi hi hYi hu hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    dsimp only
    rw [rectangle_in_jet_decomposition, ← hjv s ⟨hs.1,hs.2.trans hu.2⟩ v hv]

end EmcsfAcExtension.Local.Broad
