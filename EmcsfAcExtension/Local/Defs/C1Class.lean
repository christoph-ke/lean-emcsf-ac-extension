module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # Classical solutions of the reduced system

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A classical (`C¹`) solution of the reduced system on a domain `D` ("smooth solution",
charged_SF_new_version.tex:L4485–4490, charged_SF_new_version.tex:L6064–6199): all nine fields are
`C¹` on `D`, the
  reduced equations hold pointwise
off the axis with the partial derivatives taken within `D`, signs, and the regular-axis
conditions. -/
structure IsC1Solution (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) : Prop where
  /-- The `subset` clause of `IsC1Solution` in internal project record. -/
  subset : D ⊆ {p | p.1 ≤ p.2}
  /-- The `r_pos` clause of `IsC1Solution` in internal project record. -/
  r_pos : ∀ p ∈ D, p.1 < p.2 → 0 < S.r p.1 p.2
  /-- The `lam_pos` clause of `IsC1Solution` in internal project record. -/
  lam_pos : ∀ p ∈ D, 0 < S.lam p.1 p.2
  /-- The `nu_neg` clause of `IsC1Solution` in internal project record. -/
  nu_neg : ∀ p ∈ D, S.nu p.1 p.2 < 0
  /-- The `one_sub_mu_pos` clause of `IsC1Solution` in internal project record. -/
  one_sub_mu_pos : ∀ p ∈ D, 0 < 1 - S.mu p.1 p.2
  /-- The `c1_r` clause of `IsC1Solution` in internal project record. -/
  c1_r : ContDiffOn ℝ 1 (Function.uncurry S.r) D
  /-- The `c1_lam` clause of `IsC1Solution` in internal project record. -/
  c1_lam : ContDiffOn ℝ 1 (Function.uncurry S.lam) D
  /-- The `c1_nu` clause of `IsC1Solution` in internal project record. -/
  c1_nu : ContDiffOn ℝ 1 (Function.uncurry S.nu) D
  /-- The `c1_m` clause of `IsC1Solution` in internal project record. -/
  c1_m : ContDiffOn ℝ 1 (Function.uncurry S.m) D
  /-- The `c1_Q` clause of `IsC1Solution` in internal project record. -/
  c1_Q : ContDiffOn ℝ 1 (Function.uncurry S.Q) D
  /-- The `c1_phi` clause of `IsC1Solution` in internal project record. -/
  c1_phi : ContDiffOn ℝ 1 (Function.uncurry S.phi) D
  /-- The `c1_A` clause of `IsC1Solution` in internal project record. -/
  c1_A : ContDiffOn ℝ 1 (Function.uncurry S.A) D
  /-- The `c1_theta` clause of `IsC1Solution` in internal project record. -/
  c1_theta : ContDiffOn ℝ 1 (Function.uncurry S.theta) D
  /-- The `c1_xi` clause of `IsC1Solution` in internal project record. -/
  c1_xi : ContDiffOn ℝ 1 (Function.uncurry S.xi) D
  /-- The `eq_v` clause of `IsC1Solution` in internal project record. -/
  eq_v : ∀ p ∈ D, p.1 < p.2 →
    pdV D S.r p.1 p.2 = S.lam p.1 p.2 ∧ pdV D S.nu p.1 p.2 = S.rUV p.1 p.2 ∧
    pdV D S.m p.1 p.2 = S.mV p.1 p.2 ∧ pdV D S.Q p.1 p.2 = S.QV e p.1 p.2 ∧
    pdV D S.A p.1 p.2 = S.AV p.1 p.2 ∧ pdV D S.phi p.1 p.2 = S.phiV p.1 p.2 ∧
    pdV D S.xi p.1 p.2 = S.xiV e p.1 p.2
  /-- The `eq_u` clause of `IsC1Solution` in internal project record. -/
  eq_u : ∀ p ∈ D, p.1 < p.2 →
    pdU D S.r p.1 p.2 = S.nu p.1 p.2 ∧ pdU D S.lam p.1 p.2 = S.rUV p.1 p.2 ∧
    pdU D S.m p.1 p.2 = S.mU p.1 p.2 ∧ pdU D S.Q p.1 p.2 = S.QU e p.1 p.2 ∧
    pdU D S.phi p.1 p.2 = S.phiU e p.1 p.2 ∧ pdU D S.theta p.1 p.2 = S.thetaU e p.1 p.2
  /-- The `axis` clause of `IsC1Solution` in internal project record. -/
  axis : ∀ t, (t, t) ∈ D → S.r t t = 0 ∧ S.m t t = 0 ∧ S.Q t t = 0 ∧
    S.lam t t + S.nu t t = 0 ∧ S.a t t = S.phi t t ∧ S.b t t = S.phi t t

/-- Helper: restrict a classical solution to a subdomain with unique derivatives.
The smaller domain's unique differentiation ensures its partial derivatives agree with
those used in the original field equations. -/
theorem IsC1Solution.mono {e : ℝ} {S : Fields} {D D' : Set (ℝ × ℝ)}
    (h : IsC1Solution e S D) (hsub : D' ⊆ D) (hD' : UniqueDiffOn ℝ D') :
    IsC1Solution e S D' := by
  have hfd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
      {p : ℝ × ℝ} (hp : p ∈ D') :
      fderivWithin ℝ (Function.uncurry f) D' p =
        fderivWithin ℝ (Function.uncurry f) D p :=
    fderivWithin_subset hsub (hD' p hp) (hf.differentiableOn (by norm_num) p (hsub hp))
  refine { subset := fun _ hp => h.subset (hsub hp)
           r_pos := fun p hp => h.r_pos p (hsub hp)
           lam_pos := fun p hp => h.lam_pos p (hsub hp)
           nu_neg := fun p hp => h.nu_neg p (hsub hp)
           one_sub_mu_pos := fun p hp => h.one_sub_mu_pos p (hsub hp)
           c1_r := h.c1_r.mono hsub
           c1_lam := h.c1_lam.mono hsub
           c1_nu := h.c1_nu.mono hsub
           c1_m := h.c1_m.mono hsub
           c1_Q := h.c1_Q.mono hsub
           c1_phi := h.c1_phi.mono hsub
           c1_A := h.c1_A.mono hsub
           c1_theta := h.c1_theta.mono hsub
           c1_xi := h.c1_xi.mono hsub
           eq_v := ?_
           eq_u := ?_
           axis := fun t ht => h.axis t (hsub ht) }
  · intro p hp huv
    simpa only [pdV, hfd h.c1_r hp, hfd h.c1_nu hp, hfd h.c1_m hp, hfd h.c1_Q hp, hfd h.c1_A hp,
      hfd h.c1_phi hp, hfd h.c1_xi hp]
      using h.eq_v p (hsub hp) huv
  · intro p hp huv
    simpa only [pdU, hfd h.c1_r hp, hfd h.c1_lam hp, hfd h.c1_m hp, hfd h.c1_Q hp, hfd h.c1_phi
      hp, hfd h.c1_theta hp]
      using h.eq_u p (hsub hp) huv

/-- Helper: transport a classical solution along equality of all fields on the domain.
Within-domain derivatives depend only on the values on that domain. -/
theorem IsC1Solution.congr {e : ℝ} {S S' : Fields} {D : Set (ℝ × ℝ)}
    (h : IsC1Solution e S' D) (he : S.EqOn S' D) : IsC1Solution e S D := by
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
  have h_mu : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.mu p.1 p.2 = S'.mu p.1 p.2 := by
    intro p hp
    simp only [Fields.mu, h_m hp, h_r hp]
  have h_a : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.a p.1 p.2 = S'.a p.1 p.2 := by
    intro p hp
    simp only [Fields.a, h_phi hp, h_theta hp, h_lam hp]
  have h_b : ∀ ⦃p : ℝ × ℝ⦄, p ∈ D → S.b p.1 p.2 = S'.b p.1 p.2 := by
    intro p hp
    simp only [Fields.b, h_phi hp, h_xi hp, h_nu hp]
  have hfd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f g : ℝ → ℝ → E} (hfg : Set.EqOn (Function.uncurry f) (Function.uncurry g) D)
      {p : ℝ × ℝ} (hp : p ∈ D) :
      fderivWithin ℝ (Function.uncurry f) D p =
        fderivWithin ℝ (Function.uncurry g) D p := fderivWithin_congr' hfg hp
  refine { subset := h.subset
           r_pos := ?_
           lam_pos := ?_
           nu_neg := ?_
           one_sub_mu_pos := ?_
           c1_r := h.c1_r.congr (fun _ hp => h_r hp)
           c1_lam := h.c1_lam.congr (fun _ hp => h_lam hp)
           c1_nu := h.c1_nu.congr (fun _ hp => h_nu hp)
           c1_m := h.c1_m.congr (fun _ hp => h_m hp)
           c1_Q := h.c1_Q.congr (fun _ hp => h_Q hp)
           c1_phi := h.c1_phi.congr (fun _ hp => h_phi hp)
           c1_A := h.c1_A.congr (fun _ hp => h_A hp)
           c1_theta := h.c1_theta.congr (fun _ hp => h_theta hp)
           c1_xi := h.c1_xi.congr (fun _ hp => h_xi hp)
           eq_v := ?_
           eq_u := ?_
           axis := ?_ }
  · intro p hp huv
    simpa only [h_r hp] using h.r_pos p hp huv
  · intro p hp
    simpa only [h_lam hp] using h.lam_pos p hp
  · intro p hp
    simpa only [h_nu hp] using h.nu_neg p hp
  · intro p hp
    simpa only [h_mu hp] using h.one_sub_mu_pos p hp
  · intro p hp huv
    simpa only [pdV, hfd (fun _ hq => h_r hq) hp,
      hfd (fun _ hq => h_nu hq) hp,
      hfd (fun _ hq => h_m hq) hp,
      hfd (fun _ hq => h_Q hq) hp,
      hfd (fun _ hq => h_A hq) hp,
      hfd (fun _ hq => h_phi hq) hp,
      hfd (fun _ hq => h_xi hq) hp,
      Fields.rUV, Fields.mV, Fields.mU, Fields.QV, Fields.QU, Fields.AV, Fields.phiV, Fields.phiU,
      Fields.xiV, Fields.thetaU, Fields.waveSource,
      h_r hp, h_lam hp, h_nu hp, h_m hp, h_Q hp, h_phi hp, h_A hp, h_theta hp, h_xi hp, h_mu hp]
      using h.eq_v p hp huv
  · intro p hp huv
    simpa only [pdU, hfd (fun _ hq => h_r hq) hp,
      hfd (fun _ hq => h_lam hq) hp,
      hfd (fun _ hq => h_m hq) hp,
      hfd (fun _ hq => h_Q hq) hp,
      hfd (fun _ hq => h_phi hq) hp,
      hfd (fun _ hq => h_theta hq) hp,
      Fields.rUV, Fields.mV, Fields.mU, Fields.QV, Fields.QU, Fields.AV, Fields.phiV, Fields.phiU,
      Fields.xiV, Fields.thetaU, Fields.waveSource,
      h_r hp, h_lam hp, h_nu hp, h_m hp, h_Q hp, h_phi hp, h_A hp, h_theta hp, h_xi hp, h_mu hp]
      using h.eq_u p hp huv
  · intro t ht
    simpa only [h_r ht, h_lam ht, h_nu ht, h_m ht, h_Q ht, h_phi ht, h_A ht, h_theta ht, h_xi ht,
      h_a ht, h_b ht] using h.axis t ht

end EmcsfAcExtension.Local
