module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.GeometryTVAux
import EmcsfAcExtension.Local.Apriori.GeometryBoxMass
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Absolute continuity and both characteristic variations of mass ratio

The differentiated mass constraints are bounded in their own null
orientation. The integrable majorants include the weighted ordinary mass
budget and a polynomial charge term, so the axis endpoint is covered by
the continuous-primitive argument in approved internal project record (38)–(39).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

private theorem incoming_mu_derivative {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => S.mu x v)
      (S.nu u v / S.r u v * ((1 - S.mu u v) * ‖S.xi u v / S.nu u v‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 - S.mu u v)) (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  apply (hasDerivWithinAt_mu_u_aux hS hu huv hvT).congr_deriv
  rw [(hS.eq_u (u, v) hp huv).2.2.1]
  simp only [Fields.mU, Fields.mu, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  field_simp [(hS.r_pos (u, v) hp huv).ne', (hS.nu_neg (u, v) hp).ne]

private theorem mass_speed_bound {w r H z q m A : ℝ}
    (hw : 0 ≤ w) (hr : 0 < r) (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (hz : 0 ≤ z) (hq : 0 ≤ q) (hm : 0 ≤ m) (hqb : q ≤ A * r ^ 2) :
    |w / r * (H * z + q - m)| ≤ w / r * z + w / r * m + A * (w * r) := by
  have hHz0 := mul_nonneg hH0 hz
  have hHz1 := mul_le_mul_of_nonneg_right hH1 hz
  have hi : |H * z + q - m| ≤ z + m + q := by
    apply abs_le.mpr
    constructor <;> linarith only [hHz0, hHz1, hz, hq, hm]
  rw [abs_mul, abs_of_nonneg (div_nonneg hw hr.le)]
  calc
    _ ≤ w / r * (z + m + q) := mul_le_mul_of_nonneg_left hi (div_nonneg hw hr.le)
    _ ≤ w / r * (z + m + A * r ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hqb]) (div_nonneg hw hr.le)
    _ = _ := by field_simp

private theorem mass_speed_continuous {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => S.lam p.1 p.2 / S.r p.1 p.2 *
      ((1 - S.mu p.1 p.2) * ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ^ 2 +
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 - S.mu p.1 p.2))
      (triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) ∧
    ContinuousOn (fun p : ℝ × ℝ => S.nu p.1 p.2 / S.r p.1 p.2 *
      ((1 - S.mu p.1 p.2) * ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ^ 2 +
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 - S.mu p.1 p.2))
      (triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
  let O := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := hS.c1_r.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cl := hS.c1_lam.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cn := hS.c1_nu.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cq := hS.c1_Q.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cm := (continuousOn_mu_aux hT hS).mono (show O ⊆ triangle 0 T from inter_subset_left)
  have ct := hS.c1_theta.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cx := hS.c1_xi.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have hr (p : ℝ × ℝ) (hp : p ∈ O) := (hS.r_pos p hp.1 hp.2).ne'
  have hl (p : ℝ × ℝ) (hp : p ∈ O) := (hS.lam_pos p hp.1).ne'
  have hn (p : ℝ × ℝ) (hp : p ∈ O) := (hS.nu_neg p hp.1).ne
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hl p hp))
  have cz := cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hn p hp))
  have cH := (continuousOn_const (c := (1 : ℝ))).sub cm
  have cQ := (cq.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp))
  exact ⟨(cl.div cr hr).mul (((cH.mul (cy.norm.pow 2)).add cQ).sub cm),
    (cn.div cr hr).mul (((cH.mul (cz.norm.pow 2)).add cQ).sub cm)⟩

/-- [node restart-sec-independent-area#mass-characteristic-variation]
The mass ratio is AC on every complete axis-to-point null segment, and
both characteristic variations are bounded by `C ε²`. The positive
thresholds and `C` precede every datum and depend only on the fixed box,
uniformly in higher initial derivatives. Axis derivatives are not assumed. -/
theorem mass_characteristic_variation : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      (AbsolutelyContinuousOnInterval (S.mu u) u v ∧
        eVariationOn (S.mu u) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2)) ∧
      (AbsolutelyContinuousOnInterval (fun x => S.mu x v) u v ∧
        eVariationOn (fun x => S.mu x v) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2)) := by
  obtain ⟨ε₀, δ₁, hε₀, hδ₁, hflux⟩ := closed_quadratic_scalar_budgets
  refine ⟨ε₀, min δ₁ 1, 64, hε₀, lt_min hδ₁ (by norm_num), by norm_num, ?_⟩
  intro e T ε M S h hset hε hδ u v hu huv hvT
  let A := 4 * e ^ 2 * M ^ 2 * ε ^ 2
  have hmass := hset.weighted_mass_preclosure hu huv hvT
  have hquad := hset.quadratic_scalar_integrable hu huv hvT
  have hf := hflux e T ε M S h hset hε (hδ.trans (min_le_left _ _)) u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  have hr0 := hset.radius_nonneg hp
  have hrT : S.r u v ≤ T := (Area.radius_bounds hset hu huv hvT).2.trans
    (by linarith only [hu, hvT])
  have hd0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; have := hset.one_le_M; positivity
  have hd2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by
    nlinarith only [hd0, hδ.trans (min_le_right δ₁ 1)]
  have hE : 4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 ≤ 16 * ε ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2)
      (show 0 ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 by positivity)
    have hj := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ 16 * ε ^ 2 by positivity)
    simp only [mul_pow, sq_abs] at hj
    nlinarith only [hi, hj]
  have co := mass_speed_continuous hset.pos hset.c1
  have cm := continuousOn_mu_aux hset.pos hset.c1
  have hS := hset.c1.toIsSolution hset.pos
  have ho : outSeg u u v ⊆ triangle 0 T := by
    rintro p ⟨rfl, hx⟩; exact ⟨hu, hx.1, hx.2.trans hvT⟩
  have hi : inSeg u v v ⊆ triangle 0 T := by
    rintro p ⟨hx, hy, rfl⟩; exact ⟨hu.trans hx, hy, hvT⟩
  have po (x : ℝ) (hx : x ∈ Icc u v) : (u, x) ∈ triangle 0 T := ho ⟨rfl, hx⟩
  have pi (x : ℝ) (hx : x ∈ Icc u v) : (x, v) ∈ triangle 0 T := hi ⟨hx.1, hx.2, rfl⟩
  have bound (a b : ℝ) (hp' : (a, b) ∈ triangle 0 T) (hab : a < b)
      (w z : ℝ) (hw : 0 ≤ w) (hz : 0 ≤ z) :
      |w / S.r a b * ((1 - S.mu a b) * z + S.Q a b ^ 2 / S.r a b ^ 2 - S.mu a b)| ≤
        w / S.r a b * z + w / S.r a b * S.mu a b + A * (w * S.r a b) :=
    mass_speed_bound hw (hset.c1.r_pos (a, b) hp' hab)
      (hset.c1.one_sub_mu_pos (a, b) hp').le
      (sub_le_self _ (hset.mu_nonneg hp')) hz
      (div_nonneg (sq_nonneg _) (sq_nonneg _)) (hset.mu_nonneg hp')
      (by simpa only [A] using hset.charge_sq_div_le hp')
  constructor
  · let g := fun x => S.lam u x / S.r u x * ((1 - S.mu u x) *
      ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2 - S.mu u x)
    let B := fun x => S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2 +
      S.lam u x / S.r u x * S.mu u x + A * (S.lam u x * S.r u x)
    have imoment : IntervalIntegrable (fun x => S.lam u x * S.r u x) volume u v :=
      ((continuousOn_out_section hS.cont_lam ho).mul
        (continuousOn_out_section hS.cont_r ho)).intervalIntegrable_of_Icc huv
    have iB : IntervalIntegrable B volume u v :=
      (hquad.1.add hmass.1.1).add (imoment.const_mul A)
    have hb := ac_and_variation_le_of_interior_speed huv
      (continuousOn_out_section cm ho)
      (co.1.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => ⟨po x ⟨hx.1.le, hx.2.le⟩, hx.1⟩))
      (fun x hx => (Stab.outgoing_mu_derivative_identity hset.c1 hu hx.1
        (hx.2.le.trans hvT)).hasDerivAt (Icc_mem_nhds hx.1 (hx.2.trans_le hvT)))
      iB (fun x hx => bound u x (po x ⟨hx.1.le, hx.2.le⟩) hx.1
        (S.lam u x) _ (hset.c1.lam_pos (u, x) (po x ⟨hx.1.le, hx.2.le⟩)).le (sq_nonneg _))
    refine ⟨hb.1, hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [intervalIntegral.integral_add (hquad.1.add hmass.1.1) (imoment.const_mul A),
      intervalIntegral.integral_add hquad.1 hmass.1.1, intervalIntegral.integral_const_mul]
    have hm := outgoing_radius_moment hS huv ho 1
    norm_num only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
    rw [hm]
    dsimp only [A]
    nlinarith only [hmass.1.2, hf.1, hE, sq_nonneg ε]
  · let g := fun x => S.nu x v / S.r x v * ((1 - S.mu x v) *
      ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2 - S.mu x v)
    let B := fun x => -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2 +
      -S.nu x v / S.r x v * S.mu x v + A * ((-S.nu x v) * S.r x v)
    have imoment : IntervalIntegrable (fun x => (-S.nu x v) * S.r x v) volume u v :=
      ((continuousOn_in_section hS.cont_nu hi).neg.mul
        (continuousOn_in_section hS.cont_r hi)).intervalIntegrable_of_Icc huv
    have iB : IntervalIntegrable B volume u v :=
      (hquad.2.add hmass.2.1).add (imoment.const_mul A)
    have hb := ac_and_variation_le_of_interior_speed huv
      (continuousOn_in_section cm hi)
      (co.2.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun x hx => ⟨pi x ⟨hx.1.le, hx.2.le⟩, hx.2⟩))
      (fun x hx => (incoming_mu_derivative hset.c1 (hu.trans hx.1.le) hx.2 hvT).hasDerivAt
        (Icc_mem_nhds (hu.trans_lt hx.1) hx.2))
      iB (fun x hx => by
        change |S.nu x v / S.r x v * ((1 - S.mu x v) *
          ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2 - S.mu x v)| ≤ B x
        have hn : S.nu x v / S.r x v * ((1 - S.mu x v) *
            ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2 - S.mu x v) =
            -((-S.nu x v) / S.r x v * ((1 - S.mu x v) *
              ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2 - S.mu x v)) := by ring
        rw [hn, abs_neg]
        exact bound x v (pi x ⟨hx.1.le, hx.2.le⟩) hx.2 (-S.nu x v) _
          (neg_pos.mpr (hset.c1.nu_neg (x, v) (pi x ⟨hx.1.le, hx.2.le⟩))).le (sq_nonneg _))
    refine ⟨hb.1, hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [intervalIntegral.integral_add (hquad.2.add hmass.2.1) (imoment.const_mul A),
      intervalIntegral.integral_add hquad.2 hmass.2.1, intervalIntegral.integral_const_mul]
    have hm := incoming_radius_moment_of_solution hS huv hi 1
    norm_num only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
    rw [hm]
    dsimp only [A]
    nlinarith only [hmass.2.2, hf.2, hE, sq_nonneg ε]

end EmcsfAcExtension.Local
