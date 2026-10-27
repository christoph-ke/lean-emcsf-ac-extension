module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
public import EmcsfAcExtension.Frozen.Fields.NormalizedIn
public import EmcsfAcExtension.Frozen.Fields.Mu
public import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # Continuation bound

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Continuation bound of internal project record: all nine primary fields, both normalized scalars and
their
full within-domain first derivatives, with nondegeneracy margins (internal project record;
charged_SF_new_version.tex:L6287–6293). The finite bound `B` may depend on `T`, `|e|`, the datum and
its
first derivative, as specified by internal project record. -/
def C1BoundOn (S : Fields) (D : Set (ℝ × ℝ)) (B : ℝ) : Prop :=
  ∀ p ∈ D, B⁻¹ ≤ S.lam p.1 p.2 ∧ B⁻¹ ≤ -S.nu p.1 p.2 ∧ B⁻¹ ≤ 1 - S.mu p.1 p.2 ∧
    (∀ f ∈ ({S.r, S.lam, S.nu, S.m, S.Q, S.A} : Set (ℝ → ℝ → ℝ)),
      ‖f p.1 p.2‖ ≤ B ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ B) ∧
    (∀ f ∈ ({S.phi, S.theta, S.xi, S.a, S.b} : Set (ℝ → ℝ → ℂ)),
      ‖f p.1 p.2‖ ≤ B ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ B)

/-- Helper: restrict the continuation bound to a relatively open subdomain.
The neighborhood condition preserves the germ of the domain and hence `fderivWithin`,
without a differentiability premise. The same `B`, with its original parameter dependence,
is retained. Arbitrary domain shrinkage is not asserted. -/
theorem C1BoundOn.mono {S : Fields} {D D' : Set (ℝ × ℝ)} {B : ℝ}
    (h : C1BoundOn S D B) (hsub : D' ⊆ D)
    (hlocal : ∀ p ∈ D', D' ∈ 𝓝[D] p) : C1BoundOn S D' B := by
  intro p hp
  obtain ⟨hl, hn, hm, hr, hc⟩ := h p (hsub hp)
  have hfd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → ℝ → E) : fderivWithin ℝ (Function.uncurry f) D' p =
        fderivWithin ℝ (Function.uncurry f) D p := by
    obtain ⟨U, hU, hUD⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hlocal p hp)
    have hsets : D' ∩ U = D ∩ U := by
      ext q
      exact ⟨fun hq => ⟨hsub hq.1, hq.2⟩, fun hq => ⟨hUD ⟨hq.2, hq.1⟩, hq.2⟩⟩
    rw [← fderivWithin_inter hU, hsets, fderivWithin_inter hU]
  refine ⟨hl, hn, hm, ?_, ?_⟩
  · intro f hf
    simpa only [hfd f] using hr f hf
  · intro f hf
    simpa only [hfd f] using hc f hf

/-- Helper: transport the continuation bound along equality of fields on the domain.
The same `B` and its permitted parameter dependence are retained. -/
theorem C1BoundOn.congr {S S' : Fields} {D : Set (ℝ × ℝ)} {B : ℝ}
    (he : S.EqOn S' D) (h : C1BoundOn S' D B) : C1BoundOn S D B := by
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
  intro p hp
  obtain ⟨hl, hn, hm, hr, hc⟩ := h p hp
  have hbound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f g : ℝ → ℝ → E} (hfg : Set.EqOn (Function.uncurry f) (Function.uncurry g) D)
      (hb : ‖g p.1 p.2‖ ≤ B ∧ ‖fderivWithin ℝ (Function.uncurry g) D p‖ ≤ B) :
      ‖f p.1 p.2‖ ≤ B ∧ ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤ B := by
    rw [show f p.1 p.2 = g p.1 p.2 from hfg hp, fderivWithin_congr' hfg hp]
    exact hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [h_lam hp] using hl
  · simpa only [h_nu hp] using hn
  · simpa only [h_mu hp] using hm
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbound (fun _ hq => h_r hq) (hr S'.r (by simp))
    · exact hbound (fun _ hq => h_lam hq) (hr S'.lam (by simp))
    · exact hbound (fun _ hq => h_nu hq) (hr S'.nu (by simp))
    · exact hbound (fun _ hq => h_m hq) (hr S'.m (by simp))
    · exact hbound (fun _ hq => h_Q hq) (hr S'.Q (by simp))
    · exact hbound (fun _ hq => h_A hq) (hr S'.A (by simp))
  · intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · exact hbound (fun _ hq => h_phi hq) (hc S'.phi (by simp))
    · exact hbound (fun _ hq => h_theta hq) (hc S'.theta (by simp))
    · exact hbound (fun _ hq => h_xi hq) (hc S'.xi (by simp))
    · exact hbound (g := S'.a) (fun _ hq => h_a hq) (hc S'.a (by simp))
    · exact hbound (g := S'.b) (fun _ hq => h_b hq) (hc S'.b (by simp))

end EmcsfAcExtension.Local
