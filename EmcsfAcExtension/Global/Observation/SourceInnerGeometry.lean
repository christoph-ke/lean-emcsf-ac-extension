module

public import EmcsfAcExtension.Global.Observation.SourceGeometry
public import EmcsfAcExtension.Global.Observation.ChartComposition
public import EmcsfAcExtension.Global.Observation.InnerOptics
import Mathlib

/-! # The actual inner geometry and component equations

The source fields are pulled back through the constructed inner clock.
Compactness and complete triangles remain statements about the original
development; optical upper bounds follow from its signed curvature.
Source: charged_SF_new_version.tex:L2587–2608, L2741–2755; approved internal project record.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Supply every geometric, continuity, optical and component-equation field
of the inner normalization record from a complete constructed window
and the prior source bounds on the actual outer chart. Both optical
upper bounds are derived, rather than assumed. The old source bounds
are discharged by the source geometry/core consumers. All constants and
cutoffs precede the physical fields; no new constants or gauge occur. -/
theorem source_inner_geometry_of_window
    {e ui s a b rStar rho Lzero L K c δ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s) (hρ : 0 < rho) (hK : 0 ≤ K)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (F G U V : ℝ ≃o ℝ)
    (hF : ContDiff ℝ 1 (F : ℝ → ℝ)) (hG : ContDiff ℝ 1 (G : ℝ → ℝ))
    (hU : ContDiff ℝ 1 (U : ℝ → ℝ)) (hV : ContDiff ℝ 1 (V : ℝ → ℝ))
    (hUp : ∀ x, 0 < deriv (U : ℝ → ℝ) x) (hVp : ∀ x, 0 < deriv (V : ℝ → ℝ) x)
    (hboundary :
      let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
      let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
      ∀ t ∈ Icc (-K) K,
        (U t, V t) ∈ sidewaysTruncation P D a b Lzero L ∧ P.r (U t) (V t) = Lzero ∧
        (nullPullback P U V).nu t t = -1 / 2 ∧ (nullPullback P U V).lam t t = 1 / 2)
    (himage :
      let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
      let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
      let Q := nullPullback P U V
      let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
      ∀ p ∈ sidewaysTruncation Q E (-K) K rho Lzero,
        (U p.1, V p.2) ∈ sidewaysTruncation P D a b rStar L ∧
        c ≤ -Q.nu p.1 p.2 ∧ c ≤ Q.lam p.1 p.2)
    (hold :
      let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
      let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
      ∀ p ∈ sidewaysTruncation P D a b rStar L,
        P.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - P.mu p.1 p.2 ∧ P.rUV p.1 p.2 ≤ 0 ∧
        (HasDerivAt (P.r p.1) (P.lam p.1 p.2) p.2 ∧
          HasDerivAt (P.nu p.1) (P.rUV p.1 p.2) p.2 ∧
          HasDerivAt (P.m p.1) (P.mV p.1 p.2) p.2 ∧
          HasDerivAt (P.Q p.1) (P.QV (s * e) p.1 p.2) p.2 ∧
          HasDerivAt (P.A p.1) (P.AV p.1 p.2) p.2 ∧
          HasDerivAt (P.phi p.1) (P.phiV p.1 p.2) p.2 ∧
          HasDerivAt (P.xi p.1) (P.xiV (s * e) p.1 p.2) p.2) ∧
        (HasDerivAt (fun u => P.r u p.2) (P.nu p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.lam u p.2) (P.rUV p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.m u p.2) (P.mU p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.Q u p.2) (P.QU (s * e) p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.phi u p.2) (P.phiU (s * e) p.1 p.2) p.1 ∧
          HasDerivAt (fun u => P.theta u p.2) (P.thetaU (s * e) p.1 p.2) p.1)) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
    let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
    let Q := nullPullback P U V
    let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
    let R := sidewaysTruncation Q E (-K) K rho Lzero
    IsCompact R ∧ (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) ∧
      (ContinuousOn (Function.uncurry Q.r) R ∧ ContinuousOn (Function.uncurry Q.nu) R ∧
        ContinuousOn (Function.uncurry Q.lam) R ∧ ContinuousOn (Function.uncurry Q.A) R ∧
        ContinuousOn (Function.uncurry Q.phi) R ∧ ContinuousOn (Function.uncurry Q.theta) R ∧
        ContinuousOn (Function.uncurry Q.m) R ∧ ContinuousOn (Function.uncurry Q.Q) R ∧
        ContinuousOn (Function.uncurry Q.xi) R) ∧
      (∀ p ∈ R, -Q.nu p.1 p.2 ∈ Icc c (1 / 2) ∧ Q.lam p.1 p.2 ∈ Icc c (1 / 2) ∧
        Q.m p.1 p.2 ∈ Icc 0 2 ∧ δ ≤ 1 - Q.mu p.1 p.2) ∧
      ∀ p ∈ R,
        HasDerivAt (fun u => Q.r u p.2) (Q.nu p.1 p.2) p.1 ∧
        HasDerivAt (Q.r p.1) (Q.lam p.1 p.2) p.2 ∧
        HasDerivAt (Q.m p.1) (Q.mV p.1 p.2) p.2 ∧
        HasDerivAt (fun u => Q.lam u p.2) (Q.rUV p.1 p.2) p.1 ∧
        HasDerivAt (fun u => Q.theta u p.2) (Q.thetaU (s * e) p.1 p.2) p.1 ∧
        HasDerivAt (Q.nu p.1) (Q.rUV p.1 p.2) p.2 ∧
        HasDerivAt (Q.xi p.1) (Q.xiV (s * e) p.1 p.2) p.2 := by
  let P := nullPullback (rescaleFields (gaugeFields e S χ) s) F G
  let D := {p : ℝ × ℝ | (s * F p.1, s * G p.2) ∈ origDomain ui}
  let Q := nullPullback P U V
  let E := {p : ℝ × ℝ | (U p.1, V p.2) ∈ D}
  let R := sidewaysTruncation Q E (-K) K rho Lzero
  let Fnew := U.trans F
  let Gnew := V.trans G
  have hcompose : Q = nullPullback (rescaleFields (gaugeFields e S χ) s) Fnew Gnew :=
    nullPullback_comp_of_c1_maps _ F G U V hF hG hU hV
  have hE : E = {p : ℝ × ℝ | (s * Fnew p.1, s * Gnew p.2) ∈ origDomain ui} := rfl
  have hFnew : ContDiff ℝ 1 (Fnew : ℝ → ℝ) := hF.comp hU
  have hGnew : ContDiff ℝ 1 (Gnew : ℝ → ℝ) := hG.comp hV
  have hKK : -K ≤ K := by linarith only [hK]
  have hi : ui ≤ s * Fnew (-K) := (hboundary (-K) (left_mem_Icc.mpr hKK)).1.1.1.1
  have hu : s * Fnew K < 0 := (hboundary K (right_mem_Icc.mpr hKK)).1.1.1.2.1
  have hv : s * Gnew K ≤ 0 := (hboundary K (right_mem_Icc.mpr hKK)).1.1.1.2.2.2
  have hdiag (t) (ht : t ∈ Icc (-K) K) :
      (nullPullback (rescaleFields (gaugeFields e S χ) s) Fnew Gnew).r t t = Lzero := by
    rw [← hcompose]
    exact (hboundary t ht).2.1
  have hcompact : IsCompact R := by
    change IsCompact (sidewaysTruncation Q E (-K) K rho Lzero)
    rw [hcompose, hE]
    exact isCompact_actual_chart_truncation hS hs χ hχ Fnew Gnew hFnew hGnew
      Fnew.monotone Gnew.monotone hi hu hv
  have htri : ∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R := by
    intro p hp
    change sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation Q E (-K) K rho Lzero
    rw [hcompose, hE]
    apply actual_chart_subtriangles hS hs hρ χ Fnew Gnew Fnew.monotone Gnew.monotone hi hv hdiag p
    change p ∈ sidewaysTruncation Q E (-K) K rho Lzero at hp
    rwa [hcompose, hE] at hp
  have fields := chart_fields_continuousOn hS χ hχ Fnew Gnew hFnew hGnew R
    (fun p hp => hp.1.1)
  rw [← hcompose] at fields
  have hEq (p) (hp : p ∈ R) :=
    nullPullback_equations P U V (s * e) p.1 p.2 (deriv (U : ℝ → ℝ) p.1)
      (deriv (V : ℝ → ℝ) p.2)
      (hU.differentiable (by norm_num) p.1).hasDerivAt
      (hV.differentiable (by norm_num) p.2).hasDerivAt (hUp _) (hVp _)
      (hold _ (himage p hp).1).2.2.2.1 (hold _ (himage p hp).1).2.2.2.2
  have hMixed (p) (hp : p ∈ R) : Q.rUV p.1 p.2 ≤ 0 := by
    have hrhs := (nullPullback_rhs P U V (s * e) p.1 p.2
      (deriv (U : ℝ → ℝ) p.1) (deriv (V : ℝ → ℝ) p.2)
      (hU.differentiable (by norm_num) p.1).hasDerivAt
      (hV.differentiable (by norm_num) p.2).hasDerivAt (hUp _) (hVp _)).1
    rw [hrhs]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hUp _).le (hVp _).le)
      (hold _ (himage p hp).1).2.2.1
  have hUpper := inner_expansion_upper_of_component_equations fields.2.1 fields.2.2.1 htri
    (fun p hp => (hEq p hp).1.2.1) (fun p hp => (hEq p hp).2.2.1) hMixed
    (fun t ht => ⟨(hboundary t ht).2.2.1, (hboundary t ht).2.2.2⟩)
  refine ⟨hcompact, htri, fields, ?_, ?_⟩
  · intro p hp
    have hi' := himage p hp
    have ho := hold _ hi'.1
    exact ⟨⟨hi'.2.1, (hUpper p hp).1⟩, ⟨hi'.2.2, (hUpper p hp).2⟩, ho.1, ho.2.1⟩
  · intro p hp
    rcases hEq p hp with
      ⟨⟨hrOut, hnOut, hmOut, _hQOut, _hAOut, _hphiOut, hxiOut⟩,
        ⟨hrIn, hlIn, _hmIn, _hQIn, _hphiIn, hthetaIn⟩⟩
    exact ⟨hrIn, hrOut, hmOut, hlIn, hthetaIn, hnOut, hxiOut⟩

end EmcsfAcExtension.Global.Observation
