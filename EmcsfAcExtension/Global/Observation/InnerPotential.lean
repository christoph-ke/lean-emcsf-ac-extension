module

public import EmcsfAcExtension.Global.Observation.Potential
import Mathlib

/-! # A uniform potential bound through the fixed inner radius

The global relative-charge and mass bounds give `|Q| ≤ 2 sqrt L`.
After multiplication by the physical coupling scale the outer radius
cancels, leaving a coefficient fixed before the physical solution.
Source: charged_SF_new_version.tex:L2390–2404, L2587–2608; approved internal project record (A),
(N0).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

private theorem potential_density_bound {r lam nu Q g δ Qmax : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hlam : 0 ≤ lam) (hnu : |nu| ≤ 1 / 2)
    (hQ : |Q| ≤ Qmax) (hg : δ ≤ g) :
    |2 * Q * nu * lam / (g * r ^ 2)| ≤ (Qmax / δ) * (lam / r ^ 2) := by
  have hgp : 0 < g := hδ.trans_le hg
  have hQmax : 0 ≤ Qmax := (abs_nonneg _).trans hQ
  have hprod : 2 * |Q| * |nu| ≤ Qmax := by
    have hh := mul_le_mul hQ hnu (abs_nonneg _) hQmax
    nlinarith only [hh]
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg hlam, abs_of_pos (mul_pos hgp (sq_pos_of_pos hr))]
  calc
    _ ≤ (Qmax * lam) / (g * r ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hlam)
        (mul_pos hgp (sq_pos_of_pos hr)).le
    _ ≤ (Qmax * lam) / (δ * r ^ 2) :=
      div_le_div_of_nonneg_left (mul_nonneg hQmax hlam)
        (mul_pos hδ (sq_pos_of_pos hr)) (mul_le_mul_of_nonneg_right hg (sq_nonneg r))
    _ = _ := by ring

/-- [internal]
The outward-anchored potential has the exact majorant `Qmax/(δ r)`
on any complete positive-radius outgoing segment. `δ,Qmax` precede
all fields and labels, uniformly in its length. The source consumer
supplies the actual component equations and source mass/charge box;
no potential estimate or transformed solution class is assumed. -/
theorem potential_on_outgoing_of_mass_charge_bounds
    (δ Qmax : ℝ) (hδ : 0 < δ) (hQmax : 0 ≤ Qmax)
    (S : Fields) {u v : ℝ} (hvu : v ≤ u)
    (cr : ContinuousOn (S.r u) (Icc v u)) (cl : ContinuousOn (S.lam u) (Icc v u))
    (cA : ContinuousOn (S.A u) (Icc v u)) (cn : ContinuousOn (S.nu u) (Icc v u))
    (cQ : ContinuousOn (S.Q u) (Icc v u)) (cm : ContinuousOn (S.m u) (Icc v u))
    (hdR : ∀ t ∈ Ioo v u, HasDerivAt (S.r u) (S.lam u t) t)
    (hdA : ∀ t ∈ Ioo v u, HasDerivAt (S.A u) (S.AV u t) t)
    (hAzero : S.A u u = 0)
    (hbox : ∀ t ∈ Icc v u,
      0 < S.r u t ∧ 0 ≤ S.lam u t ∧ |S.nu u t| ≤ 1 / 2 ∧
      |S.Q u t| ≤ Qmax ∧ δ ≤ 1 - S.mu u t) :
    |S.A u v| ≤ Qmax / (δ * S.r u v) := by
  have hpos (t) (ht : t ∈ Icc v u) := (hbox t ht).1
  have cg : ContinuousOn (fun t => 1 - S.mu u t) (Icc v u) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr
      (fun t ht => (hpos t ht).ne'))
  have cf : ContinuousOn (S.AV u) (Icc v u) := by
    change ContinuousOn (fun t => 2 * S.nu u t * S.lam u t * S.Q u t /
      ((1 - S.mu u t) * S.r u t ^ 2)) (Icc v u)
    exact (((continuousOn_const.mul cn).mul cl).mul cQ).div (cg.mul (cr.pow 2))
      (fun t ht => mul_ne_zero (hδ.trans_le (hbox t ht).2.2.2.2).ne'
        (pow_ne_zero 2 (hpos t ht).ne'))
  have ck : ContinuousOn (fun t => S.lam u t / S.r u t ^ 2) (Icc v u) :=
    cl.div (cr.pow 2) (fun t ht => pow_ne_zero 2 (hpos t ht).ne')
  have ik := ck.intervalIntegrable_of_Icc (μ := volume) hvu
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvu cA hdA
    (cf.intervalIntegrable_of_Icc hvu)
  have dk (t) (ht : t ∈ Ioo v u) :
      HasDerivAt (fun x => -(S.r u x)⁻¹) (S.lam u t / S.r u t ^ 2) t := by
    simpa only [Pi.inv_apply, Pi.neg_apply, neg_div, neg_neg] using!
      ((hdR t ht).inv (hpos t (Ioo_subset_Icc_self ht)).ne').neg
  have hkernel := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvu
    ((cr.inv₀ (fun t ht => (hpos t ht).ne')).neg) dk ik
  have hkernelBound : (∫ t in v..u, S.lam u t / S.r u t ^ 2) ≤ 1 / S.r u v := by
    rw [hkernel]
    simp only [Pi.neg_apply, Pi.inv_apply, one_div]
    have hh := (inv_pos.mpr (hpos u (right_mem_Icc.mpr hvu))).le
    linarith only [hh]
  calc
    |S.A u v| = |∫ t in v..u, S.AV u t| := by rw [hFTC, hAzero, zero_sub, abs_neg]
    _ ≤ ∫ t in v..u, |S.AV u t| := intervalIntegral.abs_integral_le_integral_abs hvu
    _ ≤ ∫ t in v..u, (Qmax / δ) * (S.lam u t / S.r u t ^ 2) :=
      intervalIntegral.integral_mono_on hvu (cf.intervalIntegrable_of_Icc hvu).abs
        (ik.const_mul (Qmax / δ)) (fun t ht => by
          simpa only [Fields.AV, mul_assoc, mul_left_comm, mul_comm] using
            potential_density_bound (hpos t ht) hδ (hbox t ht).2.1
              (hbox t ht).2.2.1 (hbox t ht).2.2.2.1 (hbox t ht).2.2.2.2)
    _ = (Qmax / δ) * (∫ t in v..u, S.lam u t / S.r u t ^ 2) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (Qmax / δ) * (1 / S.r u v) :=
      mul_le_mul_of_nonneg_left hkernelBound (div_nonneg hQmax hδ.le)
    _ = Qmax / (δ * S.r u v) := by ring

/-- [internal]
The coarse global bound `|Q| ≤ 2 sqrt L` is sufficient for a uniform
charged potential bound. Its exact coefficient depends only on `δ,rStar`,
uniformly in outer scale, scalar background, coupling and potential.
The potential helper above supplies `hA`; no new constant is selected. -/
theorem charged_potential_of_sqrt_scale_bound
    {δ rStar r L e eta A : ℝ} {H : ℂ}
    (hδ : 0 < δ) (hrStar : 0 < rStar) (hr : rStar ≤ r) (hL : 1 ≤ L)
    (hscale : |e| * L * (1 + ‖H‖) = eta)
    (hA : |A| ≤ 2 * Real.sqrt L / (δ * r)) :
    |e * A| * (1 + ‖H‖) ≤ (2 / (δ * rStar)) * eta := by
  have hrp : 0 < r := hrStar.trans_le hr
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : Real.sqrt L ≤ L := (Real.sqrt_le_iff).mpr ⟨hLp.le, by nlinarith only [hL]⟩
  have hbound : |A| ≤ 2 * L / (δ * rStar) := hA.trans
    ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
      (mul_pos hδ hrp).le).trans
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * L) (mul_pos hδ hrStar)
        (mul_le_mul_of_nonneg_left hr hδ.le)))
  rw [abs_mul]
  calc
    |e| * |A| * (1 + ‖H‖) ≤ |e| * (2 * L / (δ * rStar)) * (1 + ‖H‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (abs_nonneg e)) (by positivity)
    _ = (2 / (δ * rStar)) * eta := by rw [← hscale]; ring

end EmcsfAcExtension.Global.Observation
