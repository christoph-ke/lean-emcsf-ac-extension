module

public import EmcsfAcExtension.Local.Limit.Construct2Scalar
import EmcsfAcExtension.Local.Limit.Scalar
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Natural scalar AC limits from the actual comparison input

Uniform scalar convergence and ordinary derivative Cauchy control are both
derived from the full smooth comparison. The landed family completeness
theorem then identifies the ordinary natural characteristic limits.
Renormalized mixed-density identification remains a separate step.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem exists_uniform_scalar_limit {F : ℕ → (ℝ × ℝ) → ℂ} {D : Set (ℝ × ℝ)}
    (hF : UniformCauchySeqOn F atTop D) :
    ∃ f : (ℝ × ℝ) → ℂ, TendstoUniformlyOn F f atTop D := by
  classical
  have hex : ∀ p, ∃ z : ℂ, p ∈ D → Tendsto (fun n => F n p) atTop (𝓝 z) := by
    intro p
    by_cases hp : p ∈ D
    · obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (hF.cauchySeq hp)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hp' => (hp hp').elim⟩
  choose f hf using hex
  exact ⟨f, hF.tendstoUniformlyOn_of_tendsto hf⟩

/-- Construct uniform limits of `a`, `b`, and `phi`, and identify the first
two as their ordinary natural characteristic AC limits with section-uniform
L¹ derivative convergence. The comparison threshold depends only on `A`,
uniformly in all data and derivative suprema. This is a scalar construction
helper; it asserts neither `StrongLimit` nor frozen solution membership. -/
theorem Null.scalar_natural_ac_limits_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        ∃ a b phi : ℝ → ℝ → ℂ,
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).a)
            (Function.uncurry a) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).b)
            (Function.uncurry b) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi)
            (Function.uncurry phi) atTop (triangle 0 T) ∧
          (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (a u) u T) ∧
          (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => b u v) 0 v) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
            (∫ v in u..T, ‖deriv ((Sn n).a u) v - deriv (a u) v‖) < ρ) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
            (∫ u in (0 : ℝ)..v,
              ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => b u v) u‖) < ρ) := by
  obtain ⟨ηu, hηu, hu⟩ := Null.scalar_uniform_cauchy_of_inputs hstab A hA
  obtain ⟨ηd, hηd, hd⟩ := Null.scalar_derivative_cauchy_of_inputs hstab A hA
  refine ⟨min ηu ηd, lt_min hηu hηd, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  obtain ⟨hca, hcb, hcphi⟩ := hu T e ε M Sn hn h hs hac hv hlim
    (hsmall.trans (min_le_left _ _))
  obtain ⟨hda, hdb⟩ := hd T e ε M Sn hn h hs hac hv hlim
    (hsmall.trans (min_le_right _ _))
  obtain ⟨fa, hfa⟩ := exists_uniform_scalar_limit hca
  obtain ⟨fb, hfb⟩ := exists_uniform_scalar_limit hcb
  obtain ⟨fp, hfp⟩ := exists_uniform_scalar_limit hcphi
  let a := Function.curry fa
  let b := Function.curry fb
  let phi := Function.curry fp
  have haF n (i : Icc (0 : ℝ) T) :
      AbsolutelyContinuousOnInterval ((Sn n).a i.1) i.1 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.2]
    exact (hs n).c1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨i.property.1, hv.1, hv.2⟩)
  have hbF n (i : Icc (0 : ℝ) T) :
      AbsolutelyContinuousOnInterval (fun u => (Sn n).b u i.1) 0 i.1 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le i.property.1]
    exact (hs n).c1.c1_b.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun u hu => ⟨hu.1, hu.2, i.property.2⟩)
  have hla : TendstoUniformlyOn
      (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).a p.1.1 p.2)
      (fun p => a p.1.1 p.2) atTop {p | p.2 ∈ Icc p.1.1 T} := by
    apply (hfa.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.1.1, p.2))).mono
    intro p hp
    exact ⟨p.1.property.1, hp.1, hp.2⟩
  have hlb : TendstoUniformlyOn
      (fun n (p : Icc (0 : ℝ) T × ℝ) => (Sn n).b p.2 p.1.1)
      (fun p => b p.2 p.1.1) atTop {p | p.2 ∈ Icc 0 p.1.1} := by
    apply (hfb.comp (fun p : Icc (0 : ℝ) T × ℝ => (p.2, p.1.1))).mono
    intro p hp
    exact ⟨hp.1, hp.2, p.1.property.2⟩
  obtain ⟨hacA, hstrongA, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := fun i : Icc (0 : ℝ) T => i.1) (t := fun _ => T)
    (f := fun i x => a i.1 x)
    (fun i => i.property.2) haF hla (by
      intro ρ hρ
      obtain ⟨N, hN⟩ := hda ρ hρ
      exact ⟨N, fun n hn' m hm' i => hN n hn' m hm' i.1 i.property⟩)
  obtain ⟨hacB, hstrongB, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := fun _ : Icc (0 : ℝ) T => (0 : ℝ)) (t := fun i => i.1)
    (f := fun i u => b u i.1)
    (fun i => i.property.1) hbF hlb (by
      intro ρ hρ
      obtain ⟨N, hN⟩ := hdb ρ hρ
      exact ⟨N, fun n hn' m hm' i => hN n hn' m hm' i.1 i.property⟩)
  refine ⟨a, b, phi, hfa, hfb, hfp, fun u hu => hacA ⟨u, hu⟩,
    fun v hv' => hacB ⟨v, hv'⟩, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hstrongA ρ hρ
    exact ⟨N, fun n hn' u hu => hN n hn' ⟨u, hu⟩⟩
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hstrongB ρ hρ
    exact ⟨N, fun n hn' v hv' => hN n hn' ⟨v, hv'⟩⟩

end EmcsfAcExtension.Local
