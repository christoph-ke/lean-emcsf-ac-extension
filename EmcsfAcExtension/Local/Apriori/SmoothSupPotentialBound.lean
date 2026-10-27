module

public import EmcsfAcExtension.Local.Apriori.SmoothSupCenter
public import EmcsfAcExtension.Local.Apriori.SmoothSupPotentialIdentity
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Algebra.Radial
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Uniform incoming potential derivative

The quotient-rule source is bounded before integrating its outgoing
transport. Cubic charge supplies the radius cancellation in the terms
containing the derivative of the denominator.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem real_endpoint_bound {a b C : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (cg : ContinuousOn g (Icc a b)) (dg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x)
    (bg : ∀ x ∈ Ioo a b, |deriv g x| ≤ C) : |g b - g a| ≤ C * (b - a) := by
  have hd : DifferentiableOn ℝ g (interior (Icc a b)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact (dg x hx).differentiableWithinAt
  have hp := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le cg hd (by
    intro x hx
    rw [interior_Icc] at hx
    exact (abs_le.mp (bg x hx)).2) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  have hn := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv cg hd (C := -C) (by
    intro x hx
    rw [interior_Icc] at hx
    exact (abs_le.mp (bg x hx)).1) a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  apply abs_le.mpr
  constructor <;> linarith only [hp, hn]

private theorem quotient_bound {r T d n l q du nu lu qu Q U G V : ℝ}
    (hr : 0 < r) (hrT : r ≤ T) (hd : 1 / 2 ≤ d) (hd1 : d ≤ 1)
    (hn : |n| ≤ 1) (hl : |l| ≤ 1) (hq : |q| ≤ Q * r ^ 3)
    (hdu : |du| ≤ U * r) (hnu : |nu| ≤ G) (hlu : |lu| ≤ G)
    (hqu : |qu| ≤ V * r ^ 2) (hQ : 0 ≤ Q) (hU : 0 ≤ U) (hG : 0 ≤ G) (hV : 0 ≤ V) :
    |(2 * (nu * l + n * lu) * q + 2 * n * l * qu) / (d * r ^ 2) -
      (2 * n * l * q) * (-du * r ^ 2 + d * (2 * r * n)) / (d * r ^ 2) ^ 2| ≤
        2 * (4 * G * Q * T + 2 * V) + 8 * Q * (U * T ^ 2 + 2) := by
  have hT : 0 < T := hr.trans_le hrT
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hnum : |2 * (nu * l + n * lu) * q + 2 * n * l * qu| ≤
      (4 * G * Q * T + 2 * V) * r ^ 2 := by
    calc
      _ ≤ |2 * (nu * l + n * lu) * q| + |2 * n * l * qu| := abs_add_le _ _
      _ ≤ 2 * (G * 1 + 1 * G) * (Q * r ^ 3) + 2 * 1 * 1 * (V * r ^ 2) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
        apply (abs_add_le _ _).trans
        simpa only [abs_mul] using add_le_add
          (mul_le_mul hnu hl (abs_nonneg _) hG)
          (mul_le_mul hn hlu (abs_nonneg _) (by norm_num))
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hrT
          (show 0 ≤ 4 * G * Q * r ^ 2 by positivity)
        nlinarith only [hh]
  have hden : |-du * r ^ 2 + d * (2 * r * n)| ≤ (U * T ^ 2 + 2) * r := by
    calc
      _ ≤ |-du * r ^ 2| + |d * (2 * r * n)| := abs_add_le _ _
      _ ≤ (U * r) * r ^ 2 + 1 * (2 * r * 1) := by
        simp only [abs_mul, abs_neg, abs_of_pos hr, abs_of_pos hd0,
          abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        gcongr
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrT 2)
          (show 0 ≤ U * r by positivity)
        nlinarith only [hh]
  have hN : |2 * n * l * q| ≤ 2 * Q * r ^ 3 := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * 1 * 1 * (Q * r ^ 3) := by gcongr
      _ = _ := by ring
  apply (abs_sub _ _).trans
  simp only [abs_div, abs_pow, abs_of_pos (mul_pos hd0 (sq_pos_of_pos hr))]
  rw [abs_mul]
  calc
    _ ≤ ((4 * G * Q * T + 2 * V) * r ^ 2) / ((1 / 2) * r ^ 2) +
        ((2 * Q * r ^ 3) * ((U * T ^ 2 + 2) * r)) / ((1 / 2) * r ^ 2) ^ 2 := by
      gcongr
    _ = _ := by field_simp; ring

private theorem scalar_norm {n r D : ℝ} {x : ℂ} (hn : n ≠ 0)
    (hn1 : |n| ≤ 1) (hr : 0 ≤ r) (hD : 0 ≤ D) (hx : ‖x / (n : ℂ)‖ ≤ D * r) :
    ‖x‖ ≤ D * r := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs] at hx
  have hh := (div_le_iff₀ (abs_pos.mpr hn)).mp hx
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hn1 (mul_nonneg hD hr))

/-- A scalar center-decay budget and the incoming expansion partials
bound the full incoming potential partial. `B` is chosen after the
displayed `e,R,M,D,G` and before all solution parameters and fields.
No estimate on a second derivative is assumed. -/
theorem smooth_potential_partial_of_bound (e R M D G : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G) :
    ∃ B : ℝ, 0 < B ∧ ∀ (T ε : ℝ) (S : Fields) (h : ℝ → ℂ), T ≤ R →
      AprioriSetting e T ε M S h →
      (∀ q ∈ triangle 0 T,
        ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
        ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2) →
      (∀ q ∈ triangle 0 T,
        |pdU (triangle 0 T) S.nu q.1 q.2| ≤ G ∧
        |pdU (triangle 0 T) S.lam q.1 q.2| ≤ G) →
      ∀ u v, (u, v) ∈ triangle 0 T → |pdU (triangle 0 T) S.A u v| ≤ B := by
  let Q := 2 * |e| * M * D
  let V := |e| * M * D
  let E := 4 * e ^ 2 * M ^ 2 * D ^ 2 * R ^ 2
  let U := D ^ 2 + E + 2 * (D ^ 2 + E)
  let C := 2 * (4 * G * Q * R + 2 * V) + 8 * Q * (U * R ^ 2 + 2)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨1 + C * R, by positivity, ?_⟩
  intro T ε S h hTR hset hdecay hexp
  have hT := hset.pos
  have hpow := pow_le_pow_left₀ hT.le hTR 2
  have hbound (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
      let μu := 2 * pdU (triangle 0 T) S.m u v / S.r u v -
        2 * S.m u v * S.nu u v / S.r u v ^ 2
      let N := 2 * S.nu u v * S.lam u v * S.Q u v
      let Nu := 2 * (pdU (triangle 0 T) S.nu u v * S.lam u v +
        S.nu u v * pdU (triangle 0 T) S.lam u v) * S.Q u v +
          2 * S.nu u v * S.lam u v * S.QU e u v
      let d := (1 - S.mu u v) * S.r u v ^ 2
      let du := -μu * S.r u v ^ 2 + (1 - S.mu u v) * (2 * S.r u v * S.nu u v)
      |Nu / d - N * du / d ^ 2| ≤ C := by
    have hr := hset.c1.r_pos (u, v) hp huv
    have hrR : S.r u v ≤ R :=
      ((smooth_radius_bounds_aux hset hp).2).trans (by linarith only [hp.1, hp.2.2, hTR])
    have hn := hset.c1.nu_neg (u, v) hp
    have hl := hset.c1.lam_pos (u, v) hp
    have hn1 : |S.nu u v| ≤ 1 := by
      rw [abs_of_neg hn]
      exact (hset.box _ hp).2.2.2.1
    have hl1 : |S.lam u v| ≤ 1 := by
      rw [abs_of_pos hl]
      exact (hset.box _ hp).2.1
    have hμ0 := hset.mu_nonneg hp
    have hd0 := hset.c1.one_sub_mu_pos (u, v) hp
    have hd1 : 1 - S.mu u v ≤ 1 := by linarith only [hμ0]
    have hq0 : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hq : S.Q u v ^ 2 / S.r u v ^ 2 ≤ E * S.r u v ^ 2 := by
      apply (smooth_charge_square_of_bound hset hD (fun q hq => (hdecay q hq).1) hp).trans
      dsimp only [E]
      gcongr
    have hμ : S.mu u v ≤ 2 * (D ^ 2 + E) * S.r u v ^ 2 := by
      apply ((smooth_mass_center_of_bound hset hD (fun q hq => (hdecay q hq).1) hp).2).trans
      dsimp only [E]
      gcongr
    have hg := pow_le_pow_left₀ (norm_nonneg _) (hdecay (u, v) hp).2 2
    have hμe := Stab.outgoing_mu_derivative_identity_algebra hr.ne' hn.ne
      (hset.c1.eq_u (u, v) hp huv).2.2.1
    change (2 * pdU (triangle 0 T) S.m u v / S.r u v -
      2 * S.m u v * S.nu u v / S.r u v ^ 2) = S.nu u v / S.r u v *
      ((1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v) at hμe
    have hμub : |2 * pdU (triangle 0 T) S.m u v / S.r u v -
        2 * S.m u v * S.nu u v / S.r u v ^ 2| ≤ U * S.r u v := by
      rw [hμe, abs_mul, abs_div, abs_of_pos hr]
      have hb : |(1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
          S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v| ≤ U * S.r u v ^ 2 := by
        calc
          _ ≤ |(1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
              S.Q u v ^ 2 / S.r u v ^ 2| + |S.mu u v| := abs_sub _ _
          _ = (1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
              S.Q u v ^ 2 / S.r u v ^ 2 + S.mu u v := by
            rw [abs_of_nonneg (add_nonneg (mul_nonneg hd0.le (sq_nonneg _)) hq0),
              abs_of_nonneg hμ0]
          _ ≤ 1 * (D * S.r u v) ^ 2 + E * S.r u v ^ 2 +
              2 * (D ^ 2 + E) * S.r u v ^ 2 := by gcongr
          _ = _ := by dsimp only [U]; ring
      calc
        _ ≤ 1 / S.r u v * (U * S.r u v ^ 2) := by gcongr
        _ = _ := by field_simp
    have hqu : |S.QU e u v| ≤ V * S.r u v ^ 2 := by
      have hx := scalar_norm hn.ne hn1 hr.le hD (hdecay (u, v) hp).2
      rw [Fields.QU, abs_mul, abs_mul, abs_of_pos hr]
      calc
        _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.xi u v‖) := by
          gcongr
          simpa only [norm_mul, RCLike.norm_conj] using
            Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.xi u v)
        _ ≤ |e| * S.r u v * (M * (D * S.r u v)) := by
          gcongr
          exact (hset.box (u, v) hp).2.2.2.2.2.1
        _ = _ := by dsimp only [V]; ring
    exact quotient_bound hr hrR (hset.box _ hp).2.2.2.2.1 hd1 hn1 hl1
      (smooth_charge_cubic_of_bound hset hD (fun q hq => (hdecay q hq).1) hp)
      hμub (hexp (u, v) hp).1 (hexp (u, v) hp).2 hqu hQ hU hG hV
  intro u v hp
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ T at hp
  rcases eq_or_lt_of_le hp.2.1 with rfl | huv
  · rw [(smooth_potential_axis_partials_aux hT hset.c1 hset.data ⟨hp.1, hp.2.2⟩).1,
      abs_zero]
    positivity
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have cg : ContinuousOn (fun x => pdU (triangle 0 T) S.A u x) (Icc u v) :=
    (continuousOn_pdU hset.c1.c1_A (uniqueDiffOn_triangle hT)).comp
      (continuous_const.prodMk continuous_id).continuousOn hs
  have hderiv (x : ℝ) (hx : x ∈ Ioo u v) :
      ‖deriv (fun y => pdU (triangle 0 T) S.A u y) x‖ ≤ C := by
    have hd := (smooth_potential_mixed_aux hset.c1 hp.1 hx.1
      (hx.2.le.trans hp.2.2)).hasDerivAt (Icc_mem_nhds hx.1 (hx.2.trans_le hp.2.2))
    rw [hd.deriv, Real.norm_eq_abs]
    exact hbound u x (hs ⟨hx.1.le, hx.2.le⟩) hx.1
  have hh := real_endpoint_bound huv.le cg
    (fun x hx => ((smooth_potential_mixed_aux hset.c1 hp.1 hx.1
      (hx.2.le.trans hp.2.2)).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le hp.2.2))).differentiableAt)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hderiv x hx)
  rw [(smooth_potential_axis_partials_aux hT hset.c1 hset.data
    ⟨hp.1, hp.2.1.trans hp.2.2⟩).1, sub_zero] at hh
  have hl : v - u ≤ R := by linarith only [hp.1, hp.2.2, hTR]
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hl hC])

end EmcsfAcExtension.Local
