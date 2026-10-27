module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.PotentialIncomingIdentity
import EmcsfAcExtension.Local.Stability.GeomStrongRegularity
import EmcsfAcExtension.Local.Calculus.AxisRates
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous classical representatives for the potential constraint

The cubic charge factor and the natural incoming scalar constraint
remove the radial denominators in the differentiated potential density.
This is regularity only: no derivative bound enters any estimate constant.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The totalized outgoing potential density is continuous on the
complete classical triangle and vanishes on the diagonal. There is no
size, derivative-bound or estimate-constant assumption. -/
theorem stab_potential_constraint_continuous_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry S.AV) (triangle 0 T) := by
  obtain ⟨q, cq, hq, ha⟩ := exists_continuous_charge_square_ratio_aux hset.pos hset.c1
  have cB := ((hset.c1.c1_nu.continuousOn.const_mul 2).mul hset.c1.c1_lam.continuousOn).div
    (continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1))
    (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  apply (cB.mul cq).congr
  rintro ⟨u, v⟩ hp
  rcases hp.2.1.eq_or_lt with heq | hlt
  · change u = v at heq
    subst v
    simp only [Function.uncurry_def, Pi.mul_apply, Pi.div_apply, Pi.sub_apply,
      ha u ⟨hp.1, hp.2.2⟩, mul_zero, Fields.AV, (hset.c1.axis u hp).1,
      zero_pow (by decide : 2 ≠ 0), div_zero]
  · simp only [Function.uncurry_def, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
    rw [hq u v hp hlt]
    dsimp only [Fields.AV]
    field_simp

/-- The charge divided by `r³` has a continuous representative on the
classical triangle. Only its off-axis identification is asserted; its
axis value is selected by the cubic radial factor, without choosing a
constant or asserting that the totalized quotient has that value. -/
theorem stab_exists_continuous_charge_cubic_ratio_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ∃ q : ℝ × ℝ → ℝ, ContinuousOn q (triangle 0 T) ∧
      ∀ u v, (u, v) ∈ triangle 0 T → u < v → q (u, v) = S.Q u v / S.r u v ^ 3 := by
  obtain ⟨R, cR, hR, hrf, _⟩ := exists_positive_radius_factor_aux hset.pos hset.c1
  obtain ⟨q, cq, hq⟩ := exists_continuous_charge_cubic_factor_aux hset.pos hset.c1
  refine ⟨fun p => q p / R p ^ 3, cq.div (cR.pow 3)
    (fun p hp => pow_ne_zero 3 (hR p hp).ne'), ?_⟩
  intro u v hp huv
  rw [hrf u v hp, hq u v hp]
  field_simp [(sub_pos.mpr huv).ne', (hR (u, v) hp).ne']

/-- [internal]
The incoming derivative density of the potential constraint has a
continuous representative on the complete C¹ triangle. Its formula is
identified off the axis by internal project record A11p; no artificial value is imposed
on the diagonal and no estimate constant or second derivative is assumed.
-/
theorem stab_exists_continuous_potential_incoming_source_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ∃ H : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry H) (triangle 0 T) ∧
      ∀ u v, 0 ≤ u → u < v → v ≤ T →
        HasDerivWithinAt (fun t => S.AV t v) (H u v) (Icc 0 v) u := by
  obtain ⟨q, cq, hq⟩ := stab_exists_continuous_charge_cubic_ratio_c1 hset
  let B := fun p : ℝ × ℝ => 2 * S.nu p.1 p.2 * S.lam p.1 p.2 / (1 - S.mu p.1 p.2)
  let P := fun p : ℝ × ℝ => pdU (triangle 0 T) S.phi p.1 p.2 +
    I * e * S.A p.1 p.2 * S.phi p.1 p.2
  let Z := fun p : ℝ × ℝ => (starRingEnd ℂ (S.phi p.1 p.2) *
    (P p / (S.nu p.1 p.2 : ℂ))).im
  let H := fun p : ℝ × ℝ => S.AV p.1 p.2 * geomN (triangle 0 T) S p.1 p.2 -
    2 * S.nu p.1 p.2 * B p * q p +
    (2 * e * S.nu p.1 p.2 ^ 2 * S.lam p.1 p.2 / (1 - S.mu p.1 p.2)) * Z p
  have cB : ContinuousOn B (triangle 0 T) := by
    exact ((hset.c1.c1_nu.continuousOn.const_mul 2).mul hset.c1.c1_lam.continuousOn).div
      (continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1))
      (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  have cP : ContinuousOn P (triangle 0 T) := by
    exact (continuousOn_partial_u hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)).add
      (((Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn).const_mul (I *
          e)).mul
        hset.c1.c1_phi.continuousOn)
  have cZ : ContinuousOn Z (triangle 0 T) := by
    exact Complex.continuous_im.comp_continuousOn (hset.c1.c1_phi.continuousOn.star.mul
      (cP.div (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_nu.continuousOn)
        (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg p hp).ne)))
  have cCoeff : ContinuousOn (fun p : ℝ × ℝ =>
      2 * e * S.nu p.1 p.2 ^ 2 * S.lam p.1 p.2 / (1 - S.mu p.1 p.2)) (triangle 0 T) :=
    (((hset.c1.c1_nu.continuousOn.pow 2).const_mul (2 * e)).mul hset.c1.c1_lam.continuousOn).div
      (continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1))
      (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  have cH : ContinuousOn H (triangle 0 T) := by
    exact (((stab_potential_constraint_continuous_c1 hset).mul (stab_geomN_continuous_c1 hset)).sub
      (((hset.c1.c1_nu.continuousOn.const_mul 2).mul cB).mul cq)).add (cCoeff.mul cZ)
  refine ⟨fun u v => H (u, v), cH, ?_⟩
  intro u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  apply (Stab.potential_constraint_incoming_derivative_c1 hset.c1 hu huv hvT).congr_deriv
  have hξ := xi_eq_radius_covariant_partial_aux hset.pos hset.c1 hp
  have hr := (hset.c1.r_pos (u, v) hp huv).ne'
  have hn := (hset.c1.nu_neg (u, v) hp).ne
  have hg := (hset.c1.one_sub_mu_pos (u, v) hp).ne'
  dsimp only [H, B, Z, P]
  rw [hq u v hp huv, hξ]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, Fields.AV, Complex.div_ofReal_im, Complex.div_ofReal_re]
  field_simp

end EmcsfAcExtension.Local
