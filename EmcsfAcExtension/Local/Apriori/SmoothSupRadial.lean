module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.AxisLimits
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Radial bounds used to recover scalar derivatives

The radius comparison and the linear center decay behind internal project record (N1–N2).
All coefficients are fixed numbers in the bootstrap box; they are uniform in
the coupling, triangle, datum, and derivative bound.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

private theorem radius_u_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    pdU (triangle 0 T) S.r u v = S.nu u v :=
  eqOn_triangle_of_offAxis hT (continuousOn_pdU hS.c1_r (uniqueDiffOn_triangle hT))
    hS.c1_nu.continuousOn (fun p hp huv => (hS.eq_u p hp huv).1) hp

private theorem radius_increment_out_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {u a b : ℝ}
    (hu : 0 ≤ u) (hua : u ≤ a) (hab : a ≤ b) (hbT : b ≤ T) :
    S.r u b - S.r u a = ∫ x in a..b, S.lam u x := by
  have hs : MapsTo (fun x => (u, x)) (Icc a b) (triangle 0 T) :=
    fun _ hx => ⟨hu, hua.trans hx.1, hx.2.trans hbT⟩
  have hi := integralForm_pdV hS.c1_r (uniqueDiffOn_triangle hT) hab hs
  rw [hi.2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact hS.pdV_r hT (hs hx)

private theorem radius_increment_in_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {a b v : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (hvT : v ≤ T) :
    S.r b v - S.r a v = ∫ x in a..b, S.nu x v := by
  have hs : MapsTo (fun x => (x, v)) (Icc a b) (triangle 0 T) :=
    fun _ hx => ⟨ha.trans hx.1, hx.2.trans hbv, hvT⟩
  have hi := integralForm_pdU hS.c1_r (uniqueDiffOn_triangle hT) hab hs
  rw [hi.2]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact radius_u_aux hS hT (hs hx)

/-- The outgoing radius is its positive radial density integrated from the
axis. There are no constants. The positive-time condition is internal project record. -/
theorem smooth_radius_integral_out_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) : (∫ x in u..v, S.lam u x) = S.r u v := by
  have hi := radius_increment_out_aux hS hT hp.1 le_rfl hp.2.1 hp.2.2
  simpa only [(hS.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩).1, sub_zero] using hi.symm

/-- The incoming radius is the density `-ν` integrated backwards from the
axis. There are no constants. The positive-time condition is internal project record. -/
theorem smooth_radius_integral_in_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) : (∫ x in u..v, -S.nu x v) = S.r u v := by
  have hi := radius_increment_in_aux hS hT hp.1 hp.2.1 le_rfl hp.2.2
  rw [(hS.axis v ⟨hp.1.trans hp.2.1, le_rfl, hp.2.2⟩).1, zero_sub] at hi
  rw [intervalIntegral.integral_neg, ← hi, neg_neg]

/-- Radius and coordinate separation are comparable with exact universal
coefficients `1/4` and `1` in the standing bootstrap box. -/
theorem smooth_radius_bounds_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    (v - u) / 4 ≤ S.r u v ∧ S.r u v ≤ v - u := by
  have hrad := radius_increment_out_aux hset.c1 hset.pos hp.1 le_rfl hp.2.1 hp.2.2
  rw [(hset.c1.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩).1, sub_zero] at hrad
  have hl : (∫ _ in u..v, (1 / 4 : ℝ)) ≤ ∫ x in u..v, S.lam u x := by
    apply intervalIntegral.integral_mono_on hp.2.1 (intervalIntegrable_const)
      ((hset.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩)).intervalIntegrable_of_Icc hp.2.1)
    intro x hx
    exact (hset.box (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩).1
  have hh : (∫ x in u..v, S.lam u x) ≤ ∫ _ in u..v, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on hp.2.1
      ((hset.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩)).intervalIntegrable_of_Icc hp.2.1)
      intervalIntegrable_const
    intro x hx
    exact (hset.box (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩).2.1
  rw [← hrad, intervalIntegral.integral_const] at hl hh
  simp only [smul_eq_mul, mul_one] at hl hh
  constructor <;> linarith only [hl, hh]

private theorem radius_order_out_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {u x v : ℝ}
    (hu : 0 ≤ u) (hux : u ≤ x) (hxv : x ≤ v) (hvT : v ≤ T) :
    S.r u x ≤ S.r u v := by
  have hi := radius_increment_out_aux hS hT hu hux hxv hvT
  have hpos : 0 ≤ ∫ t in x..v, S.lam u t :=
    intervalIntegral.integral_nonneg hxv (fun t ht =>
      (hS.lam_pos (u, t) ⟨hu, hux.trans ht.1, ht.2.trans hvT⟩).le)
  linarith only [hi, hpos]

private theorem radius_order_in_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) {u x v : ℝ}
    (hu : 0 ≤ u) (hux : u ≤ x) (hxv : x ≤ v) (hvT : v ≤ T) :
    S.r x v ≤ S.r u v := by
  have hi := radius_increment_in_aux hS hT hu hux hxv hvT
  have hpos : 0 ≤ ∫ t in u..x, -S.nu t v :=
    intervalIntegral.integral_nonneg hux (fun t ht =>
      neg_nonneg.mpr (hS.nu_neg (t, v) ⟨hu.trans ht.1, ht.2.trans hxv, hvT⟩).le)
  rw [intervalIntegral.integral_neg] at hpos
  have hneg : (∫ t in u..x, S.nu t v) ≤ 0 := neg_nonneg.mp hpos
  linarith only [hi, hneg]

/-- A bound on the outgoing normalized derivative gives linear center decay.
The literal coefficient `4` is independent of all parameters, including `A`.
This helper uses the proved Hardy moment, without a curvature identity. -/
theorem smooth_outgoing_decay_of_bound {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hA : 0 ≤ A)
    (hb : ∀ p ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a p.1 p.2‖ ≤ A)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    ‖S.theta u v / S.lam u v‖ ≤ 4 * S.r u v * A := by
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ T at hp
  rcases hp.2.1.eq_or_lt with heq | huv
  · subst v
    have ha := (hset.c1.axis u hp).2.2.2.2.1
    have hz : S.theta u u / (S.lam u u : ℂ) = 0 := by
      simpa only [Fields.a, add_eq_left] using ha
    simp only [hz, norm_zero, (hset.c1.axis u hp).1, mul_zero, zero_mul, le_refl]
  have hr := hset.c1.r_pos (u, v) hp huv
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
      fun _ hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩)
  have cd := (continuousOn_pdV hset.c1.c1_a (uniqueDiffOn_triangle hset.pos)).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (show MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) from
      fun _ hx => ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩)
  have hi : (∫ x in u..v, S.r u x * ‖pdV (triangle 0 T) S.a u x‖) ≤
      S.r u v * A * (v - u) := by
    calc
      _ ≤ ∫ _ in u..v, S.r u v * A := by
        apply intervalIntegral.integral_mono_on huv.le
          ((cr.mul cd.norm).intervalIntegrable_of_Icc huv.le) intervalIntegrable_const
        intro x hx
        exact mul_le_mul
          (radius_order_out_aux hset.c1 hset.pos hp.1 hx.1 hx.2 hp.2.2)
          (hb (u, x) ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩) (norm_nonneg _) hr.le
      _ = _ := by rw [intervalIntegral.integral_const]; ring
  calc
    _ ≤ (S.r u v)⁻¹ * ∫ x in u..v, S.r u x * ‖pdV (triangle 0 T) S.a u x‖ :=
      bv_hardy_out hset.c1 hp.1 huv hp.2.2
    _ ≤ (S.r u v)⁻¹ * (S.r u v * A * (v - u)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
    _ = (v - u) * A := by field_simp [hr.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      linarith only [(smooth_radius_bounds_aux hset hp).1]) hA

/-- A bound on the covariant incoming normalized derivative gives linear
center decay with the same universal coefficient `4`. The incoming Hardy
moment already contains its unitary parallel frame. -/
theorem smooth_incoming_decay_of_bound {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hA : 0 ≤ A)
    (hb : ∀ p ∈ triangle 0 T,
      ‖pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2‖ ≤ A)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    ‖S.xi u v / S.nu u v‖ ≤ 4 * S.r u v * A := by
  change 0 ≤ u ∧ u ≤ v ∧ v ≤ T at hp
  rcases hp.2.1.eq_or_lt with heq | huv
  · subst v
    have ha := (hset.c1.axis u hp).2.2.2.2.2
    have hz : S.xi u u / (S.nu u u : ℂ) = 0 := by
      simpa only [Fields.b, add_eq_left] using ha
    simp only [hz, norm_zero, (hset.c1.axis u hp).1, mul_zero, zero_mul, le_refl]
  have hr := hset.c1.r_pos (u, v) hp huv
  have hs : MapsTo (fun x => (x, v)) (Icc u v) (triangle 0 T) :=
    fun _ hx => ⟨hp.1.trans hx.1, hx.2, hp.2.2⟩
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have cd : ContinuousOn (fun p : ℝ × ℝ =>
      pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2)
      (triangle 0 T) :=
    (continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).add
      ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
        hset.c1.c1_b.continuousOn)
  have cdi := (cd.comp (continuous_id.prodMk continuous_const).continuousOn hs).norm
  have hi : (∫ x in u..v, S.r x v *
      ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖) ≤
      S.r u v * A * (v - u) := by
    calc
      _ ≤ ∫ _ in u..v, S.r u v * A := by
        apply intervalIntegral.integral_mono_on huv.le
          ((cr.mul cdi).intervalIntegrable_of_Icc huv.le) intervalIntegrable_const
        intro x hx
        exact mul_le_mul
          (radius_order_in_aux hset.c1 hset.pos hp.1 hx.1 hx.2 hp.2.2)
          (hb (x, v) (hs hx)) (norm_nonneg _) hr.le
      _ = _ := by rw [intervalIntegral.integral_const]; ring
  calc
    _ ≤ (S.r u v)⁻¹ * ∫ x in u..v, S.r x v *
        ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ :=
      bv_hardy_in hset.c1 hp.1 huv hp.2.2
    _ ≤ (S.r u v)⁻¹ * (S.r u v * A * (v - u)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hr.le)
    _ = (v - u) * A := by field_simp [hr.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      linarith only [(smooth_radius_bounds_aux hset hp).1]) hA

end EmcsfAcExtension.Local
