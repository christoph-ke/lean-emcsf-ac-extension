module

public import EmcsfAcExtension.Local.Construction.StripCharacteristic
public import EmcsfAcExtension.Local.Construction.StripC1Map
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import EmcsfAcExtension.Local.Construction.TraceExtension
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Order.ProjIcc

/-! # Joint C¹ regularity on a continuation rectangle

The literal Goursat equations (46) of internal project record imply
joint C¹ regularity, including all four sides, for continuous solutions
with C¹ entering data and C¹ finite-dimensional sources. The proof
localizes the sources, rescales to a fixed square, and applies the Banach
implicit function theorem to the weighted Picard map. It assumes no
first jets or second derivatives of the data or solution. The resulting
transverse Volterra identities (47) are proved in `StripJets`.
-/

public section

open Set MeasureTheory Filter
open scoped Topology

namespace EmcsfAcExtension.Local

section FixedPoint

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {T : P × E → E} {F : P → E} {s : Set P} {p : P}

/-- A continuous parameterized fixed point is C¹ whenever its Picard
operator is C¹ and its derivative in the state variable has norm less
than one. The proof uses the Banach implicit function theorem, and
assumes no derivative of the fixed point. -/
theorem contDiffWithinAt_continuous_fixedPoint
    (hT : ContDiffAt ℝ 1 T (p, F p))
    (hp : p ∈ s)
    (hF : ContinuousWithinAt F s p)
    (hfix : ∀ᶠ x in 𝓝[s] p, T (x, F x) = F x)
    (hsmall : ‖fderiv ℝ T (p, F p) ∘L ContinuousLinearMap.inr ℝ P E‖ < 1) :
    ContDiffWithinAt ℝ 1 F s p := by
  let G : P × E → E := fun q => q.2 - T q
  have hG : ContDiffAt ℝ 1 G (p, F p) := contDiffAt_snd.sub hT
  have hdG : fderiv ℝ G (p, F p) =
      ContinuousLinearMap.snd ℝ P E - fderiv ℝ T (p, F p) := by
    exact ((hasFDerivAt_snd (𝕜 := ℝ) (p := (p, F p))).sub (hT.differentiableAt
        (by decide)).hasFDerivAt).fderiv
  have hinv : (fderiv ℝ G (p, F p) ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible := by
    rw [hdG, ContinuousLinearMap.sub_comp]
    have hid : ContinuousLinearMap.snd ℝ P E ∘L ContinuousLinearMap.inr ℝ P E = 1 := by
      ext x
      rfl
    rw [hid]
    obtain ⟨z, hz⟩ := isUnit_one_sub_of_norm_lt_one hsmall
    exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E z, hz⟩
  let ψ := hG.implicitFunction (by decide) hinv
  have hψ : ContDiffAt ℝ 1 ψ p := hG.contDiffAt_implicitFunction (by decide) hinv
  have heq := hG.eventually_apply_eq_iff_implicitFunction (by decide) hinv
  have htend : Tendsto (fun x => (x, F x)) (𝓝[s] p) (𝓝 (p, F p)) :=
    (continuousWithinAt_id.prodMk hF).tendsto
  have hbase : G (p, F p) = 0 := by
    dsimp [G]
    have := mem_of_mem_nhdsWithin hp hfix
    exact sub_eq_zero.mpr this.symm
  have hcongr : F =ᶠ[𝓝[s] p] ψ := by
    filter_upwards [htend.eventually heq, hfix] with x hx hfx
    have hxG : G (x, F x) = G (p, F p) := by simp [G, hfx, hbase]
    exact (hx.mp hxG).symm
  exact hψ.contDiffWithinAt.congr_of_eventuallyEq hcongr (hG.implicitFunction_apply_self (by decide)
      hinv).symm


end FixedPoint

section Joint

open StripFunctionSpace

variable {I O : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I] [CompleteSpace I]
  [NormedAddCommGroup O] [NormedSpace ℝ O] [CompleteSpace O]

/-- Joint C¹ regularity of an actual continuous Goursat solution for
compactly supported C¹ source extensions and entering traces. The proof
rescales the solution to the fixed square and applies the Banach implicit
function theorem. It assumes neither transverse jets nor second datum
or solution derivatives. Compact support is removed by localization in
the following consumer theorem. -/
theorem contDiffOn_goursat_compactSupport {a b c d : ℝ}
    (hab : a ≤ b) (_hcd : c ≤ d) (F : ℝ × ℝ → I × O) (hF : Continuous F)
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : ContDiff ℝ 1 yi) (hxb : ContDiff ℝ 1 xb)
    (hfi : ContDiff ℝ 1 fi) (hfo : ContDiff ℝ 1 fo)
    (hyiC : HasCompactSupport yi) (hxbC : HasCompactSupport xb)
    (hfiC : HasCompactSupport fi) (hfoC : HasCompactSupport fo)
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t))) :
    ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d) := by
  obtain ⟨Li, hLi⟩ := compactSupport_lipschitz hfi hfiC
  obtain ⟨Lo, hLo⟩ := compactSupport_lipschitz hfo hfoC
  let L : NNReal := max Li Lo
  have hfiL : LipschitzWith L fi := hLi.weaken (le_max_left _ _)
  have hfoL : LipschitzWith L fo := hLo.weaken (le_max_right _ _)
  let M := max (b-a) (d-c)
  have hM : 0 ≤ M := le_max_of_le_left (sub_nonneg.mpr hab)
  let γ := M * (L : ℝ) + 1
  have hγ : 0 < γ := add_pos_of_nonneg_of_pos (mul_nonneg hM L.2) zero_lt_one
  let C := M * (L : ℝ) / γ
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hM L.2) hγ.le
  have hC1 : C < 1 := (div_lt_one hγ).mpr (lt_add_one _)
  let Z := stripRescaledState a c γ F hF
  let T := stripC1Picard a c γ hγ yi xb fi fo
    hyi.continuous hxb.continuous hfi.continuous hfo.continuous
  have hT : ContDiff ℝ 1 T :=
    contDiff_stripC1Picard a c γ hγ hyi hxb hfi hfo hyiC hxbC hfiC hfoC
  have hZ : Continuous Z := continuous_stripRescaledState a c γ F hF
  intro p hp
  have hfix : ∀ᶠ x in 𝓝[Icc a b ×ˢ Icc c d] p, T (x, Z x) = Z x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact stripC1Picard_rescaled_fixedPoint hγ F hF yi xb fi fo
      hyi.continuous hxb.continuous hfi.continuous hfo.continuous hYi hXb hx
  have hmax : max |p.1-a| |p.2-c| ≤ M := by
    rw [abs_of_nonneg (sub_nonneg.mpr hp.1.1), abs_of_nonneg (sub_nonneg.mpr hp.2.1)]
    exact max_le_max (sub_le_sub_right hp.1.2 a) (sub_le_sub_right hp.2.2 c)
  have hbound (z : C(StripUnitSquare, I × O)) :
      ‖T (p,z)-T (p,Z p)‖ ≤ C * ‖z-Z p‖ := by
    calc
      _ ≤ max |p.1-a| |p.2-c| * γ⁻¹ * (L * ‖z-Z p‖) :=
        norm_stripC1Picard_sub_le a c γ hγ yi xb fi fo
          hyi.continuous hxb.continuous hfiL hfoL p z (Z p)
      _ ≤ M * γ⁻¹ * (L * ‖z-Z p‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmax (inv_nonneg.mpr hγ.le))
          (mul_nonneg L.2 (norm_nonneg _))
      _ = C * ‖z-Z p‖ := by dsimp [C]; rw [div_eq_mul_inv]; ring
  have hd := (hT.contDiffAt.differentiableAt (by decide)).hasFDerivAt.comp (Z p)
    (hasFDerivAt_prodMk_right p (Z p))
  have hsmall : ‖fderiv ℝ T (p,Z p) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ)
      C(StripUnitSquare, I × O)‖ < 1 :=
    (hd.le_of_lip' hC (Filter.Eventually.of_forall hbound)).trans_lt hC1
  have hZc1 := contDiffWithinAt_continuous_fixedPoint hT.contDiffAt hp
    hZ.continuousAt.continuousWithinAt hfix hsmall
  let q₁ : StripUnitSquare := (⟨1, zero_le_one, le_rfl⟩, ⟨1, zero_le_one, le_rfl⟩)
  have heval := (ContinuousMap.evalCLM ℝ q₁ :
    C(StripUnitSquare, I × O) →L[ℝ] I × O).contDiff.contDiffAt.comp_contDiffWithinAt p hZc1
  have hscaled := heval.const_smul (stripUnitWeight γ q₁)
  convert hscaled using 1
  ext x <;> simp [Z, stripRescaledState, q₁, smul_smul, stripUnitWeight]

/-- Joint C¹ regularity from the literal two Goursat integral equations,
C¹ entering data and sources C¹ on an open neighborhood of the actual
state range. The solution is assumed only continuous. Source and trace
extensions are constructed internally; no first-jet existence premise
or second derivative of data or solution is used. -/
theorem contDiffOn_goursat_of_integral_eq_of_continuous [FiniteDimensional ℝ I] [FiniteDimensional ℝ
    O]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (F : ℝ × ℝ → I × O) (hF : Continuous F)
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : ContDiffOn ℝ 1 yi (Icc c d)) (hxb : ContDiffOn ℝ 1 xb (Icc a b))
    (U : Set (I × O)) (hU : IsOpen U) (hFU : MapsTo F (Icc a b ×ˢ Icc c d) U)
    (hfi : ∀ z ∈ U, ContDiffAt ℝ 1 fi z) (hfo : ∀ z ∈ U, ContDiffAt ℝ 1 fo z)
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t))) :
    ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d) := by
  obtain ⟨yi₀, hyi₀, hyeq₀⟩ := exists_contDiff_one_extension_Icc hcd hyi
  obtain ⟨xb₀, hxb₀, hxeq₀⟩ := exists_contDiff_one_extension_Icc hab hxb
  obtain ⟨yi₁, hyi₁, hyiC, hyeq₁⟩ := exists_compactly_supported_extension (n := 1)
    (K := Icc c d) (U := univ) isCompact_Icc isOpen_univ (subset_univ _)
    (fun z _ => hyi₀.contDiffAt)
  obtain ⟨xb₁, hxb₁, hxbC, hxeq₁⟩ := exists_compactly_supported_extension (n := 1)
    (K := Icc a b) (U := univ) isCompact_Icc isOpen_univ (subset_univ _)
    (fun z _ => hxb₀.contDiffAt)
  have hyeq : EqOn yi₁ yi (Icc c d) := fun v hv => (hyeq₁ hv).trans (hyeq₀ hv)
  have hxeq : EqOn xb₁ xb (Icc a b) := fun u hu => (hxeq₁ hu).trans (hxeq₀ hu)
  have hK : IsCompact (F '' (Icc a b ×ˢ Icc c d)) :=
    (isCompact_Icc.prod isCompact_Icc).image hF
  have hKU : F '' (Icc a b ×ˢ Icc c d) ⊆ U := by
    rintro z ⟨p, hp, rfl⟩
    exact hFU hp
  obtain ⟨fi₁, hfi₁, hfiC, hieq⟩ :=
    exists_compactly_supported_extension (n := 1) hK hU hKU hfi
  obtain ⟨fo₁, hfo₁, hfoC, hoeq⟩ :=
    exists_compactly_supported_extension (n := 1) hK hU hKU hfo
  have hi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u,v)).1 = yi₁ v + ∫ s in a..u, fi₁ (F (s,v)) := by
    intro u hu v hv
    rw [hYi u hu v hv, hyeq hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu.1] at ht
    exact (hieq (mem_image_of_mem F ⟨⟨ht.1, ht.2.trans hu.2⟩, hv⟩)).symm
  have ho : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u,v)).2 = xb₁ u + ∫ t in c..v, fo₁ (F (u,t)) := by
    intro u hu v hv
    rw [hXb u hu v hv, hxeq hu]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    exact (hoeq (mem_image_of_mem F ⟨hu, ⟨ht.1, ht.2.trans hv.2⟩⟩)).symm
  exact contDiffOn_goursat_compactSupport hab.le hcd.le F hF yi₁ xb₁ fi₁ fo₁
    hyi₁ hxb₁ hfi₁ hfo₁ hyiC hxbC hfiC hfoC hi ho

/-- Joint C¹ regularity of a continuous state on a closed rectangle
from its literal two Goursat integral equations, C¹ entering traces and
C¹ state sources on an open neighborhood of its actual range. All four
sides are included. A continuous clamped extension is constructed inside
the proof; no regularity or field equation outside the rectangle is assumed. -/
theorem contDiffOn_goursat_of_integral_eq [FiniteDimensional ℝ I] [FiniteDimensional ℝ O]
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (F : ℝ × ℝ → I × O) (hF : ContinuousOn F (Icc a b ×ˢ Icc c d))
    (yi : ℝ → I) (xb : ℝ → O) (fi : I × O → I) (fo : I × O → O)
    (hyi : ContDiffOn ℝ 1 yi (Icc c d)) (hxb : ContDiffOn ℝ 1 xb (Icc a b))
    (U : Set (I × O)) (hU : IsOpen U) (hFU : MapsTo F (Icc a b ×ˢ Icc c d) U)
    (hfi : ∀ z ∈ U, ContDiffAt ℝ 1 fi z) (hfo : ∀ z ∈ U, ContDiffAt ℝ 1 fo z)
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t))) :
    ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d) := by
  let P : ℝ × ℝ → ℝ × ℝ := fun p =>
    (projIcc a b hab.le p.1, projIcc c d hcd.le p.2)
  have hP : Continuous P :=
    (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  let F₁ := F ∘ P
  have hF₁ : Continuous F₁ := hF.comp_continuous hP
    (fun p => ⟨(projIcc a b hab.le p.1).2,(projIcc c d hcd.le p.2).2⟩)
  have heq : EqOn F₁ F (Icc a b ×ˢ Icc c d) := by
    intro p hp
    simp [F₁, P, projIcc_of_mem hab.le hp.1, projIcc_of_mem hcd.le hp.2]
  have hFU₁ : MapsTo F₁ (Icc a b ×ˢ Icc c d) U := by
    intro p hp
    rw [heq hp]
    exact hFU hp
  have hi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F₁ (u,v)).1 = yi v + ∫ s in a..u, fi (F₁ (s,v)) := by
    intro u hu v hv
    rw [heq ⟨hu,hv⟩, hYi u hu v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu.1] at ht
    exact congrArg fi (heq ⟨⟨ht.1,ht.2.trans hu.2⟩,hv⟩).symm
  have ho : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F₁ (u,v)).2 = xb u + ∫ t in c..v, fo (F₁ (u,t)) := by
    intro u hu v hv
    rw [heq ⟨hu,hv⟩, hXb u hu v hv]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hv.1] at ht
    exact congrArg fo (heq ⟨hu,⟨ht.1,ht.2.trans hv.2⟩⟩).symm
  exact (contDiffOn_goursat_of_integral_eq_of_continuous hab hcd F₁ hF₁ yi xb fi fo
    hyi hxb U hU hFU₁ hfi hfo hi ho).congr (fun p hp => (heq hp).symm)

end Joint

end EmcsfAcExtension.Local
