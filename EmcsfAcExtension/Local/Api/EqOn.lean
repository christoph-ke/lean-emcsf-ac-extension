module

public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.Fields.Omega2
public import EmcsfAcExtension.Frozen.JOut
public import EmcsfAcExtension.Frozen.KIn
public import EmcsfAcExtension.Frozen.CovVarIn
public import EmcsfAcExtension.Frozen.Triangle

/-! # Equality on the domain and sectional congruence

Frozen derivatives agree almost everywhere on equal closed sections: only the
endpoints are discarded. No differentiability or solution hypothesis is needed.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension
namespace Fields.EqOn

variable {S S' S'' : Fields} {D D' : Set (ℝ × ℝ)}

/-- Every configuration agrees with itself on a domain. -/
theorem refl (S : Fields) (D : Set (ℝ × ℝ)) : S.EqOn S D :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Equality on a domain is symmetric. -/
@[symm] theorem symm (h : S.EqOn S' D) : S'.EqOn S D := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h p hp
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm,
    h7.symm, h8.symm, h9.symm⟩

/-- Equality on a domain is transitive. -/
@[trans] theorem trans (h : S.EqOn S' D) (h' : S'.EqOn S'' D) : S.EqOn S'' D := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h p hp
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := h' p hp
  exact ⟨h1.trans k1, h2.trans k2, h3.trans k3, h4.trans k4, h5.trans k5,
    h6.trans k6, h7.trans k7, h8.trans k8, h9.trans k9⟩

/-- Restrict equality to a smaller domain. -/
theorem mono (h : S.EqOn S' D) (hD : D' ⊆ D) : S.EqOn S' D' :=
  fun p hp => h p (hD hp)

/-- Equal configurations have equal `r` at every domain point. -/
theorem r (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.r u v = S'.r u v := (h (u, v) hp).1

/-- Equal configurations have equal `lam` at every domain point. -/
theorem lam (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.lam u v = S'.lam u v := (h (u, v) hp).2.1

/-- Equal configurations have equal `nu` at every domain point. -/
theorem nu (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.nu u v = S'.nu u v := (h (u, v) hp).2.2.1

/-- Equal configurations have equal `m` at every domain point. -/
theorem m (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.m u v = S'.m u v := (h (u, v) hp).2.2.2.1

/-- Equal configurations have equal `Q` at every domain point. -/
theorem Q (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.Q u v = S'.Q u v := (h (u, v) hp).2.2.2.2.1

/-- Equal configurations have equal `phi` at every domain point. -/
theorem phi (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.phi u v = S'.phi u v := (h (u, v) hp).2.2.2.2.2.1

/-- Equal configurations have equal `A` at every domain point. -/
theorem A (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.A u v = S'.A u v := (h (u, v) hp).2.2.2.2.2.2.1

/-- Equal configurations have equal `theta` at every domain point. -/
theorem theta (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.theta u v = S'.theta u v := (h (u, v) hp).2.2.2.2.2.2.2.1

/-- Equal configurations have equal `xi` at every domain point. -/
theorem xi (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.xi u v = S'.xi u v := (h (u, v) hp).2.2.2.2.2.2.2.2

/-- Equal configurations have equal derived field `mu` on the domain. -/
theorem mu (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.mu u v = S'.mu u v := by
  unfold Fields.mu
  rw [h.m hp, h.r hp]

/-- Equal configurations have equal derived field `a` on the domain. -/
theorem a (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.a u v = S'.a u v := by
  unfold Fields.a
  rw [h.phi hp, h.theta hp, h.lam hp]

/-- Equal configurations have equal derived field `b` on the domain. -/
theorem b (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.b u v = S'.b u v := by
  unfold Fields.b
  rw [h.phi hp, h.xi hp, h.nu hp]

/-- Equal configurations have equal derived field `Omega2` on the domain. -/
theorem Omega2 (h : S.EqOn S' D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.Omega2 u v = S'.Omega2 u v := by
  unfold Fields.Omega2
  rw [h.nu hp, h.lam hp, h.mu hp]

/-- Equality on an outgoing section transports variation of the normalized field. -/
theorem eVariationOn_a (h : S.EqOn S' D) {u a b : ℝ}
    (hs : ∀ v ∈ Icc a b, (u, v) ∈ D) :
    eVariationOn (S.a u) (Icc a b) = eVariationOn (S'.a u) (Icc a b) :=
  eVariationOn.eq_of_eqOn (fun v hv => h.a (hs v hv))

/-- Equality on an incoming section transports ordinary normalized-field variation. -/
theorem eVariationOn_b (h : S.EqOn S' D) {v a b : ℝ}
    (hs : ∀ u ∈ Icc a b, (u, v) ∈ D) :
    eVariationOn (fun u => S.b u v) (Icc a b) =
      eVariationOn (fun u => S'.b u v) (Icc a b) :=
  eVariationOn.eq_of_eqOn (fun u hu => h.b (hs u hu))

end Fields.EqOn

namespace Local

/-- Covariant variation depends only on the potential and curve on the closed section. -/
theorem covVarIn_congr {e a b v : ℝ} {A A' : ℝ → ℝ → ℝ} {f f' : ℝ → ℝ → ℂ}
    (hA : ∀ u ∈ Icc a b, A u v = A' u v)
    (hf : ∀ u ∈ Icc a b, f u v = f' u v) :
    covVarIn e A f a b v = covVarIn e A' f' a b v := by
  apply eVariationOn.eq_of_eqOn
  intro u hu
  have hi : (∫ s in a..u, A s v) = ∫ s in a..u, A' s v := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hu.1] at hs
    exact hA s ⟨hs.1, hs.2.trans hu.2⟩
  dsimp only
  rw [hi, hf u hu]

/-- Functions equal on a closed real interval have a.e. equal ordinary derivatives there. -/
theorem deriv_ae_eq_of_eqOn_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ} (h : Set.EqOn f g (Icc a b)) :
    deriv f =ᵐ[volume.restrict (Icc a b)] deriv g := by
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (h.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hx

end Local

namespace Fields.EqOn

variable {S S' : Fields} {D : Set (ℝ × ℝ)}

/-- Equal configurations have equal covariant incoming normalized-field variation. -/
theorem covVarIn_b (h : S.EqOn S' D) {e v a b : ℝ}
    (hs : ∀ u ∈ Icc a b, (u, v) ∈ D) :
    covVarIn e S.A S.b a b v = covVarIn e S'.A S'.b a b v :=
  Local.covVarIn_congr (fun u hu => h.A (hs u hu)) (fun u hu => h.b (hs u hu))

/-- The frozen outgoing density agrees a.e. on any equal outgoing closed section. -/
theorem jOut_ae (h : S.EqOn S' D) {u a b : ℝ}
    (hs : ∀ v ∈ Icc a b, (u, v) ∈ D) :
    jOut S u =ᵐ[volume.restrict (Icc a b)] jOut S' u := by
  filter_upwards [Local.deriv_ae_eq_of_eqOn_Icc (fun v hv => h.a (hs v hv)),
    ae_restrict_mem measurableSet_Icc] with v hd hv
  unfold jOut
  rw [hd, h.mu (hs v hv), h.lam (hs v hv), h.r (hs v hv), h.theta (hs v hv)]

/-- The frozen incoming density agrees a.e. on any equal incoming closed section. -/
theorem kIn_ae (h : S.EqOn S' D) {e v a b : ℝ}
    (hs : ∀ u ∈ Icc a b, (u, v) ∈ D) :
    (fun u => kIn e S u v) =ᵐ[volume.restrict (Icc a b)] (fun u => kIn e S' u v) := by
  filter_upwards [Local.deriv_ae_eq_of_eqOn_Icc (fun u hu => h.b (hs u hu)),
    ae_restrict_mem measurableSet_Icc] with u hd hu
  unfold kIn
  rw [hd, h.mu (hs u hu), h.A (hs u hu), h.b (hs u hu), h.nu (hs u hu),
    h.r (hs u hu), h.xi (hs u hu)]

end Fields.EqOn
end EmcsfAcExtension
