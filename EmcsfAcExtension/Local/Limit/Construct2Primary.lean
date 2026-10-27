module

public import EmcsfAcExtension.Local.Limit.Construct2Geometry
public import EmcsfAcExtension.Local.Limit.Construct2Scalar
import EmcsfAcExtension.Local.Limit.Construct
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Calculus.Partials

/-! # The nine primary uniform limits from strong data approximation

The comparison controls radius, expansions, mass ratio, scalar, charge and
potential directly. Products reconstruct mass and the scalar momenta. Compactness
is used only for continuity of products, without a bound on any derivative.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem exists_limit {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {F : ℕ → (ℝ × ℝ) → E} {T : ℝ}
    (hc : UniformCauchySeqOn F atTop (triangle 0 T)) :
    ∃ f, TendstoUniformlyOn F f atTop (triangle 0 T) := by
  classical
  have hx : ∀ p, ∃ z : E, p ∈ triangle 0 T → Tendsto (fun n => F n p) atTop (𝓝 z) := by
    intro p
    by_cases hp : p ∈ triangle 0 T
    · obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (hc.cauchySeq hp)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => (hp h).elim⟩
  choose f hf using hx
  exact ⟨f, hc.tendstoUniformlyOn_of_tendsto hf⟩

private theorem cauchy_mul {E : Type*} [NormedField E] [CompleteSpace E]
    {F G : ℕ → (ℝ × ℝ) → E} {T : ℝ}
    (hF : UniformCauchySeqOn F atTop (triangle 0 T))
    (hG : UniformCauchySeqOn G atTop (triangle 0 T))
    (cF : ∀ n, ContinuousOn (F n) (triangle 0 T))
    (cG : ∀ n, ContinuousOn (G n) (triangle 0 T)) :
    UniformCauchySeqOn (fun n p => F n p * G n p) atTop (triangle 0 T) := by
  obtain ⟨f, hf⟩ := exists_limit hF
  obtain ⟨g, hg⟩ := exists_limit hG
  exact ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_triangle 0 T)).1
    (hf.tendstoLocallyUniformlyOn.mul₀ hg.tendstoLocallyUniformlyOn
      (hf.continuousOn (Eventually.of_forall cF).frequently)
      (hg.continuousOn (Eventually.of_forall cG).frequently))).uniformCauchySeqOn

private theorem cauchy_congr {E : Type*} [UniformSpace E]
    {F G : ℕ → (ℝ × ℝ) → E} {T : ℝ}
    (hf : UniformCauchySeqOn F atTop (triangle 0 T))
    (heq : ∀ n p, p ∈ triangle 0 T → F n p = G n p) :
    UniformCauchySeqOn G atTop (triangle 0 T) := by
  intro U hU
  filter_upwards [hf U hU] with nm hnm p hp
  simpa only [← heq nm.1 p hp, ← heq nm.2 p hp] using hnm p hp

private theorem mass_identity {e T : ℝ} {S : Fields}
    (hc : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    S.mu p.1 p.2 * S.r p.1 p.2 / 2 = S.m p.1 p.2 := by
  rcases hp.2.1.eq_or_lt with heq | hlt
  · have hz := (hc.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).2.1
    simp only [← heq, hz, Fields.mu, mul_zero, zero_mul, zero_div]
  · unfold Fields.mu
    field_simp [(hc.r_pos p hp hlt).ne']

private theorem theta_identity {e T : ℝ} {S : Fields}
    (hc : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    (S.lam p.1 p.2 : ℂ) * (S.a p.1 p.2 - S.phi p.1 p.2) = S.theta p.1 p.2 := by
  simp only [Fields.a, add_sub_cancel_left]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hc.lam_pos p hp).ne')

private theorem xi_identity {e T : ℝ} {S : Fields}
    (hc : IsC1Solution e S (triangle 0 T)) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    (S.nu p.1 p.2 : ℂ) * (S.b p.1 p.2 - S.phi p.1 p.2) = S.xi p.1 p.2 := by
  simp only [Fields.b, add_sub_cancel_left]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hc.nu_neg p hp).ne)

/-- All nine primary fields are uniformly Cauchy on the closed triangle,
from the actual full classical comparison. The threshold depends only on
`A`, uniformly in all data, couplings, times and derivative suprema. Mass,
theta and xi use their algebraic identities and compact uniform products;
there is no extra primary-field Cauchy premise. This is the uniform component
of same-label Cauchy control, before frozen-density identification. -/
theorem Null.primary_uniform_cauchy_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).r) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).lam) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).nu) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).m) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).Q) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).phi) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).A) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).theta) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).xi) atTop (triangle 0 T) := by
  obtain ⟨ηg, hηg, hg⟩ := Null.geometry_uniform_cauchy_of_inputs hstab A hA
  obtain ⟨ηs, hηs, hs⟩ := Null.scalar_uniform_cauchy_of_inputs hstab A hA
  refine ⟨min ηg ηs, lt_min hηg hηs, ?_⟩
  intro T e ε M Sn hn h hset hac hv hlim hsmall
  obtain ⟨hr, hl, hn', hmu, hQ, hA'⟩ := hg T e ε M Sn hn h hset hac hv hlim
    (hsmall.trans (min_le_left _ _))
  obtain ⟨ha, hb, hp⟩ := hs T e ε M Sn hn h hset hac hv hlim
    (hsmall.trans (min_le_right _ _))
  have hmprod := cauchy_mul hmu hr
    (fun n => (hset n).c1.continuousOn_mu (hset n).pos)
    (fun n => (hset n).c1.c1_r.continuousOn)
  have hm : UniformCauchySeqOn (fun n => Function.uncurry (Sn n).m)
      atTop (triangle 0 T) := by
    have hh := (uniformContinuous_div_const' (2 : ℝ)).comp_uniformCauchySeqOn hmprod
    exact cauchy_congr hh (fun n p hp' => mass_identity (hset n).c1 hp')
  have hlc := Complex.isometry_ofReal.uniformContinuous.comp_uniformCauchySeqOn hl
  have hnc := Complex.isometry_ofReal.uniformContinuous.comp_uniformCauchySeqOn hn'
  have hθprod := cauchy_mul hlc (ha.sub hp)
    (fun n => Complex.continuous_ofReal.comp_continuousOn (hset n).c1.c1_lam.continuousOn)
    (fun n => (hset n).c1.c1_a.continuousOn.sub (hset n).c1.c1_phi.continuousOn)
  have hξprod := cauchy_mul hnc (hb.sub hp)
    (fun n => Complex.continuous_ofReal.comp_continuousOn (hset n).c1.c1_nu.continuousOn)
    (fun n => (hset n).c1.c1_b.continuousOn.sub (hset n).c1.c1_phi.continuousOn)
  refine ⟨hr, hl, hn', hm, hQ, hp, hA', ?_, ?_⟩
  · exact cauchy_congr hθprod (fun n p hp' => theta_identity (hset n).c1 hp')
  · exact cauchy_congr hξprod (fun n p hp' => xi_identity (hset n).c1 hp')

/-- Construct one configuration carrying all nine primary uniform limits,
without assuming any Cauchy conclusion. The positive threshold depends only
on `A`, before time, coupling, all data and all approximation families.
Identification with frozen j/k derivatives is a later construction step. -/
theorem Null.primary_uniform_limits_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        ∃ S : Fields,
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).r)
            (Function.uncurry S.r) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).lam)
            (Function.uncurry S.lam) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).nu)
            (Function.uncurry S.nu) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).m)
            (Function.uncurry S.m) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Q)
            (Function.uncurry S.Q) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi)
            (Function.uncurry S.phi) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).A)
            (Function.uncurry S.A) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).theta)
            (Function.uncurry S.theta) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).xi)
            (Function.uncurry S.xi) atTop (triangle 0 T) := by
  obtain ⟨η, hη, hc⟩ := Null.primary_uniform_cauchy_of_inputs hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  obtain ⟨hr, hl, hnu, hm, hQ, hp, hA', hθ, hξ⟩ :=
    hc T e ε M Sn hn h hs hac hv hlim hsmall
  exact exists_uniform_fields_of_cauchy hr hl hnu hm hQ hp hA' hθ hξ

end EmcsfAcExtension.Local
