module

public import EmcsfAcExtension.Frozen.Fields

/-! # Construction of the uniform limiting fields

The uniform part of the fixed-label construction at `charged_SF_new_version.tex:L6391–6446`.
The renormalized derivative identification is a separate obligation: this module
does not identify abstract mixed-norm limits with the frozen derivatives.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Local

private theorem exists_uniform_limit_of_cauchy {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {F : ℕ → (ℝ × ℝ) → E}
    (hF : UniformCauchySeqOn F atTop D) :
    ∃ f : (ℝ × ℝ) → E, TendstoUniformlyOn F f atTop D := by
  classical
  have hex : ∀ p, ∃ z : E, p ∈ D → Tendsto (fun n => F n p) atTop (𝓝 z) := by
    intro p
    by_cases hp : p ∈ D
    · obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (hF.cauchySeq hp)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hp' => (hp hp').elim⟩
  choose f hf using hex
  exact ⟨f, hF.tendstoUniformlyOn_of_tendsto hf⟩

/-- Auxiliary uniform-field construction for `charged_SF_new_version.tex:L6391–6446`.
Every field has its own uniform Cauchy hypothesis, and all nine limits belong to
one configuration. The statement holds on any domain, including an empty or
degenerate one; it introduces no estimate or selected numerical constant.
This is the uniform component of the construction, rather than a graph-node
closure or an assertion of `StrongLimit`. -/
theorem exists_uniform_fields_of_cauchy {D : Set (ℝ × ℝ)} {Sn : ℕ → Fields}
    (hr : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).r) atTop D)
    (hlam : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).lam) atTop D)
    (hnu : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).nu) atTop D)
    (hm : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).m) atTop D)
    (hQ : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).Q) atTop D)
    (hphi : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).phi) atTop D)
    (hA : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).A) atTop D)
    (htheta : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).theta) atTop D)
    (hxi : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).xi) atTop D) :
    ∃ S : Fields,
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).r) (Function.uncurry S.r) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).lam) (Function.uncurry S.lam) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).nu) (Function.uncurry S.nu) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).m) (Function.uncurry S.m) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Q) (Function.uncurry S.Q) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi) (Function.uncurry S.phi) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).A) (Function.uncurry S.A) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).theta)
        (Function.uncurry S.theta) atTop D ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Sn n).xi) (Function.uncurry S.xi) atTop D := by
  obtain ⟨r, hr⟩ := exists_uniform_limit_of_cauchy hr
  obtain ⟨lam, hlam⟩ := exists_uniform_limit_of_cauchy hlam
  obtain ⟨nu, hnu⟩ := exists_uniform_limit_of_cauchy hnu
  obtain ⟨m, hm⟩ := exists_uniform_limit_of_cauchy hm
  obtain ⟨Q, hQ⟩ := exists_uniform_limit_of_cauchy hQ
  obtain ⟨phi, hphi⟩ := exists_uniform_limit_of_cauchy hphi
  obtain ⟨A, hA⟩ := exists_uniform_limit_of_cauchy hA
  obtain ⟨theta, htheta⟩ := exists_uniform_limit_of_cauchy htheta
  obtain ⟨xi, hxi⟩ := exists_uniform_limit_of_cauchy hxi
  exact ⟨⟨Function.curry r, Function.curry lam, Function.curry nu, Function.curry m,
    Function.curry Q, Function.curry phi, Function.curry A, Function.curry theta,
    Function.curry xi⟩, hr, hlam, hnu, hm, hQ, hphi, hA, htheta, hxi⟩

end EmcsfAcExtension.Local
