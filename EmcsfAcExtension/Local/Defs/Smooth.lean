module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # Smooth solutions of the reduced system

The construction class of internal project record, separate from the classical class used for
estimates.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal ContDiff

namespace EmcsfAcExtension.Local

/-- [internal]
The smooth class produced by internal project record (`#smooth-regularity`, `#smooth-full-system`):
a classical solution with all nine primary fields smooth on the domain (internal project record). -/
structure IsSmoothSolution (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) : Prop where
  /-- The underlying classical solution. -/
  c1 : IsC1Solution e S D
  /-- Smoothness of the primary field `r` on the domain. -/
  smooth_r : ContDiffOn ℝ ∞ (Function.uncurry S.r) D
  /-- Smoothness of the primary field `lam` on the domain. -/
  smooth_lam : ContDiffOn ℝ ∞ (Function.uncurry S.lam) D
  /-- Smoothness of the primary field `nu` on the domain. -/
  smooth_nu : ContDiffOn ℝ ∞ (Function.uncurry S.nu) D
  /-- Smoothness of the primary field `m` on the domain. -/
  smooth_m : ContDiffOn ℝ ∞ (Function.uncurry S.m) D
  /-- Smoothness of the primary field `Q` on the domain. -/
  smooth_Q : ContDiffOn ℝ ∞ (Function.uncurry S.Q) D
  /-- Smoothness of the primary field `phi` on the domain. -/
  smooth_phi : ContDiffOn ℝ ∞ (Function.uncurry S.phi) D
  /-- Smoothness of the primary field `A` on the domain. -/
  smooth_A : ContDiffOn ℝ ∞ (Function.uncurry S.A) D
  /-- Smoothness of the primary field `theta` on the domain. -/
  smooth_theta : ContDiffOn ℝ ∞ (Function.uncurry S.theta) D
  /-- Smoothness of the primary field `xi` on the domain. -/
  smooth_xi : ContDiffOn ℝ ∞ (Function.uncurry S.xi) D

/-- Helper: restrict a smooth solution to a subdomain with unique derivatives.
Unique differentiation preserves the within-domain derivatives in the field equations. -/
theorem IsSmoothSolution.mono {e : ℝ} {S : Fields} {D D' : Set (ℝ × ℝ)}
    (h : IsSmoothSolution e S D) (hsub : D' ⊆ D) (hD' : UniqueDiffOn ℝ D') :
    IsSmoothSolution e S D' :=
  ⟨h.c1.mono hsub hD', (h.smooth_r).mono hsub, (h.smooth_lam).mono hsub, (h.smooth_nu).mono hsub,
      (h.smooth_m).mono hsub, (h.smooth_Q).mono hsub, (h.smooth_phi).mono hsub, (h.smooth_A).mono
      hsub, (h.smooth_theta).mono hsub, (h.smooth_xi).mono hsub⟩

/-- Helper: transport smooth solutions along equality of fields on the domain. -/
theorem IsSmoothSolution.congr {e : ℝ} {S S' : Fields} {D : Set (ℝ × ℝ)}
    (he : S.EqOn S' D) (h : IsSmoothSolution e S' D) : IsSmoothSolution e S D := by
  have h_r : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.r p.1 p.2 = S'.r p.1 p.2 :=
    fun _ hp => (he _ hp).1
  have h_lam : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.lam p.1 p.2 = S'.lam p.1 p.2 :=
    fun _ hp => (he _ hp).2.1
  have h_nu : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.nu p.1 p.2 = S'.nu p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.1
  have h_m : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.m p.1 p.2 = S'.m p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.1
  have h_Q : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.Q p.1 p.2 = S'.Q p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.2.1
  have h_phi : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.phi p.1 p.2 = S'.phi p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.2.2.1
  have h_A : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.A p.1 p.2 = S'.A p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.2.2.2.1
  have h_theta : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.theta p.1 p.2 = S'.theta p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.2.2.2.2.1
  have h_xi : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.xi p.1 p.2 = S'.xi p.1 p.2 :=
    fun _ hp => (he _ hp).2.2.2.2.2.2.2.2
  exact ⟨h.c1.congr he, h.smooth_r.congr (fun _ hp => h_r hp),
    h.smooth_lam.congr (fun _ hp => h_lam hp),
    h.smooth_nu.congr (fun _ hp => h_nu hp),
    h.smooth_m.congr (fun _ hp => h_m hp),
    h.smooth_Q.congr (fun _ hp => h_Q hp),
    h.smooth_phi.congr (fun _ hp => h_phi hp),
    h.smooth_A.congr (fun _ hp => h_A hp),
    h.smooth_theta.congr (fun _ hp => h_theta hp),
    h.smooth_xi.congr (fun _ hp => h_xi hp)⟩

end EmcsfAcExtension.Local
