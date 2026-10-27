module

public import EmcsfAcExtension.Local.Calculus.AxisContinuity
public import EmcsfAcExtension.Local.Calculus.AxisFactor
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Radius quotients continuous at the regular axis

Continuous section factors identify first-order quotients without assigning arbitrary
axis values. The radius equation then forces the mass ratio's continuous value to zero.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Divide a C¹ real field vanishing on the axis by the radius. Its continuous
extension has axis value `∂ᵥf/λ`. Only `0 < T` is added to exclude the singleton
triangle; no equation for `f` is assumed. -/
theorem exists_continuous_div_radius_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (haxis : ∀ t ∈ Icc 0 T, f t t = 0) :
    ∃ g : (ℝ × ℝ) → ℝ, ContinuousOn g (triangle 0 T) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → u < v → g (u, v) = f u v / S.r u v) ∧
      (∀ t ∈ Icc 0 T, g (t, t) = pdV (triangle 0 T) f t t / S.lam t t) := by
  obtain ⟨R, hR, hrf, hrdiag⟩ := exists_continuous_axis_factor_aux hT hS.c1_r
  obtain ⟨F, hF, hff, hfdiag⟩ := exists_continuous_axis_factor_aux hT hf
  have hr (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      S.r u v = (v - u) * R (u, v) := by
    have h := hrf u v hp
    simpa [(hS.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩).1] using h
  have hf' (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      f u v = (v - u) * F (u, v) := by
    simpa [haxis u ⟨hp.1, hp.2.1.trans hp.2.2⟩] using hff u v hp
  have hRne (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : R p ≠ 0 := by
    rcases p with ⟨u, v⟩
    by_cases huv : u < v
    · intro hz
      have h := hr u v hp
      rw [hz, mul_zero] at h
      exact (hS.r_pos _ hp huv).ne' h
    · have huv' : u = v := le_antisymm hp.2.1 (not_lt.mp huv)
      subst v
      rw [hrdiag u ⟨hp.1, hp.2.2⟩, (radius_axis_partials_aux hT hS
        ⟨hp.1, hp.2.2⟩).2]
      exact (hS.lam_pos _ hp).ne'
  refine ⟨fun p => F p / R p, hF.div hR hRne, ?_, ?_⟩
  · intro u v hp huv
    rw [hf' u v hp, hr u v hp]
    field_simp [(sub_pos.mpr huv).ne', hRne (u, v) hp]
  · intro t ht
    change F (t, t) / R (t, t) = _
    rw [hfdiag t ht, hrdiag t ht, (radius_axis_partials_aux hT hS ht).2]

/-- The charge divided by the radius has a continuous extension with zero axis
value. Maxwell's polynomial equations identify its first derivatives at the axis. -/
theorem exists_continuous_charge_ratio_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ q : (ℝ × ℝ) → ℝ, ContinuousOn q (triangle 0 T) ∧
      (∀ u v, (u, v) ∈ triangle 0 T → u < v → q (u, v) = S.Q u v / S.r u v) ∧
      (∀ t ∈ Icc 0 T, q (t, t) = 0) := by
  obtain ⟨q, hc, heq, hdiag⟩ := exists_continuous_div_radius_aux hT hS hS.c1_Q
    (fun t ht => (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.1)
  refine ⟨q, hc, heq, fun t ht => ?_⟩
  rw [hdiag t ht, (charge_axis_partials_aux hT hS ht).2, zero_div]

/-- The literal mass ratio `μ=2m/r`, with its defined axis value zero, is continuous
on a positive-time classical triangle. This is proved from the radius equation
and Maxwell regularity, without presupposing mass decay estimates. -/
theorem continuousOn_mu_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry S.mu) (triangle 0 T) := by
  obtain ⟨q, cq, hq, hqaxis⟩ := exists_continuous_charge_ratio_aux hT hS
  obtain ⟨m, cm, hmeq, _⟩ := exists_continuous_div_radius_aux hT hS hS.c1_m
    (fun t ht => (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).2.1)
  have cM : ContinuousOn (fun p => 2 * m p) (triangle 0 T) := continuousOn_const.mul cm
  have cp := continuousOn_partial_u hS.c1_lam (uniqueDiffOn_triangle hT)
  have heq : EqOn
      (fun p => S.r p.1 p.2 * pdU (triangle 0 T) S.lam p.1 p.2 * (1 - 2 * m p))
      (fun p => S.nu p.1 p.2 * S.lam p.1 p.2 * (2 * m p - q p ^ 2)) (triangle 0 T) := by
    apply eqOn_triangle_of_off_axis_aux hT
      ((hS.c1_r.continuousOn.mul cp).mul ((continuousOn_const (c := 1)).sub cM))
      ((hS.c1_nu.continuousOn.mul hS.c1_lam.continuousOn).mul (cM.sub (cq.pow 2)))
    intro p hp huv
    change S.r p.1 p.2 * pdU (triangle 0 T) S.lam p.1 p.2 * (1 - 2 * m p) =
      S.nu p.1 p.2 * S.lam p.1 p.2 * (2 * m p - q p ^ 2)
    rw [hmeq p.1 p.2 hp huv, hq p.1 p.2 hp huv, (hS.eq_u p hp huv).2.1]
    dsimp only [Fields.rUV, Fields.mu]
    have hr := (hS.r_pos p hp huv).ne'
    have hm := (hS.one_sub_mu_pos p hp).ne'
    change 1 - 2 * S.m p.1 p.2 / S.r p.1 p.2 ≠ 0 at hm
    have hden : S.r p.1 p.2 - 2 * S.m p.1 p.2 ≠ 0 := by
      intro hz
      apply hm
      field_simp [hr]
      linear_combination hz
    field_simp [hr, hm, hden]
  have haxis (t : ℝ) (ht : t ∈ Icc 0 T) : 2 * m (t, t) = 0 := by
    have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
    have h := heq hp
    dsimp only at h
    rw [(hS.axis t hp).1, zero_mul, zero_mul, hqaxis t ht, sq, mul_zero,
      sub_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (mul_ne_zero (hS.nu_neg _ hp).ne (hS.lam_pos _ hp).ne')
  apply cM.congr
  intro p hp
  rcases p with ⟨u, v⟩
  change S.mu u v = 2 * m (u, v)
  by_cases huv : u < v
  · rw [hmeq u v hp huv]
    dsimp only [Fields.mu]
    ring
  · have huv' : u = v := le_antisymm hp.2.1 (not_lt.mp huv)
    subst v
    rw [haxis u ⟨hp.1, hp.2.2⟩]
    simp only [Fields.mu, (hS.axis u hp).1, div_zero]

end EmcsfAcExtension.Local
