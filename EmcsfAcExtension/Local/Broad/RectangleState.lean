module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # The full finite-dimensional positive-radius characteristic state

The incoming block is `(λ,θ)` and the outgoing block is
`(r,ν,m,Q,A,φ,ξ)`. The source maps evaluate the literal frozen right sides.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Broad

/-- The incoming block of the full reduced characteristic system. -/
abbrev RectangleIncoming := ℝ × ℂ

/-- The outgoing block includes charge and the gauge potential. -/
abbrev RectangleOutgoing := ℝ × ℝ × ℝ × ℝ × ℝ × ℂ × ℂ

/-- The full characteristic state, with the product norm. -/
abbrev RectangleState := RectangleIncoming × RectangleOutgoing

/-- Evaluate all nine primary fields in characteristic block order. -/
@[expose] noncomputable def rectangle_state (S : Fields) (p : ℝ × ℝ) : RectangleState :=
  ((S.lam p.1 p.2, S.theta p.1 p.2),
    (S.r p.1 p.2, S.nu p.1 p.2, S.m p.1 p.2, S.Q p.1 p.2,
      S.A p.1 p.2, S.phi p.1 p.2, S.xi p.1 p.2))

/-- Realize a finite state as constant fields, for evaluation of the
frozen algebraic right sides. No equation or hypothesis is imposed. -/
@[expose] noncomputable def rectangle_constant_fields (z : RectangleState) : Fields where
  r := fun _ _ => z.2.1
  lam := fun _ _ => z.1.1
  nu := fun _ _ => z.2.2.1
  m := fun _ _ => z.2.2.2.1
  Q := fun _ _ => z.2.2.2.2.1
  A := fun _ _ => z.2.2.2.2.2.1
  phi := fun _ _ => z.2.2.2.2.2.2.1
  theta := fun _ _ => z.1.2
  xi := fun _ _ => z.2.2.2.2.2.2.2

/-- The incoming block of the literal frozen source. -/
@[expose] noncomputable def rectangle_in_source (e : ℝ) (z : RectangleState) : RectangleIncoming :=
  let S := rectangle_constant_fields z
  (S.rUV 0 0, S.thetaU e 0 0)

/-- The outgoing block of the literal frozen source. -/
@[expose] noncomputable def rectangle_out_source (e : ℝ) (z : RectangleState) : RectangleOutgoing :=
  let S := rectangle_constant_fields z
  (S.lam 0 0, S.rUV 0 0, S.mV 0 0, S.QV e 0 0, S.AV 0 0, S.phiV 0 0, S.xiV e 0 0)

/-- The convex positive-radius state region. The last condition is the
linear numerator of the positive mass gap, `r-2m>0`. -/
@[expose] def rectangle_state_region : Set RectangleState :=
  {z | 0 < z.2.1 ∧ 0 < z.1.1 ∧ 0 < z.2.1 - 2 * z.2.2.2.1}

/-- Continuity of the full characteristic state follows from the nine
primary continuity clauses of the frozen broad class. -/
theorem continuousOn_rectangle_state {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn (rectangle_state S) D :=
  (hS.cont_lam.prodMk hS.cont_theta).prodMk
    (hS.cont_r.prodMk (hS.cont_nu.prodMk (hS.cont_m.prodMk (hS.cont_Q.prodMk
      (hS.cont_A.prodMk (hS.cont_phi.prodMk hS.cont_xi))))))

/-- Equality of finite states is precisely equality of all primary fields
at the point. -/
theorem rectangle_state_eq_iff (S₁ S₂ : Fields) (p : ℝ × ℝ) :
    rectangle_state S₁ p = rectangle_state S₂ p ↔
      S₁.r p.1 p.2 = S₂.r p.1 p.2 ∧ S₁.lam p.1 p.2 = S₂.lam p.1 p.2 ∧
      S₁.nu p.1 p.2 = S₂.nu p.1 p.2 ∧ S₁.m p.1 p.2 = S₂.m p.1 p.2 ∧
      S₁.Q p.1 p.2 = S₂.Q p.1 p.2 ∧ S₁.phi p.1 p.2 = S₂.phi p.1 p.2 ∧
      S₁.A p.1 p.2 = S₂.A p.1 p.2 ∧ S₁.theta p.1 p.2 = S₂.theta p.1 p.2 ∧
      S₁.xi p.1 p.2 = S₂.xi p.1 p.2 := by
  simp only [rectangle_state, Prod.mk.injEq]
  tauto

/-- Literal evaluation of the incoming source at an actual solution state. -/
theorem rectangle_in_source_state (e : ℝ) (S : Fields) (p : ℝ × ℝ) :
    rectangle_in_source e (rectangle_state S p) = (S.rUV p.1 p.2, S.thetaU e p.1 p.2) := rfl

/-- Literal evaluation of the outgoing source at an actual solution state. -/
theorem rectangle_out_source_state (e : ℝ) (S : Fields) (p : ℝ × ℝ) :
    rectangle_out_source e (rectangle_state S p) =
      (S.lam p.1 p.2, S.rUV p.1 p.2, S.mV p.1 p.2, S.QV e p.1 p.2,
        S.AV p.1 p.2, S.phiV p.1 p.2, S.xiV e p.1 p.2) := rfl

/-- Every off-axis solution state belongs to the positive state region. -/
theorem rectangle_state_mem_region {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {p : ℝ × ℝ} (hp : p ∈ D) (hpos : p.1 < p.2) :
    rectangle_state S p ∈ rectangle_state_region := by
  have hr := hS.r_pos p hp hpos
  have hg := hS.one_sub_mu_pos p hp
  refine ⟨hr, hS.lam_pos p hp, ?_⟩
  have hh := mul_pos hg hr
  change 0 < (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2 at hh
  have heq : (1 - 2 * S.m p.1 p.2 / S.r p.1 p.2) * S.r p.1 p.2 =
      S.r p.1 p.2 - 2 * S.m p.1 p.2 := by field_simp [hr.ne']
  exact heq ▸ hh

end EmcsfAcExtension.Local.Broad
