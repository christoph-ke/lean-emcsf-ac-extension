module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.GeometryBoxMassKernel
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Weighted ordinary mass budgets in both null orientations

The outgoing mass constraint is a radial average from its axis endpoint.
The incoming constraint has the same positive form after reversing the
incoming coordinate. Each weighted kernel is applied in its own orientation
(`charged_SF_new_version.tex:L4819–L4828`, approved internal project record (24)–(27)).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- The outgoing mass constraint reconstructed from the same-axis endpoint.
This is an exact identity in the broad frozen class, with no estimate constants
or derivative envelopes. -/
private theorem outgoing_mass_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    2 * S.m u v = ∫ x in u..v, S.lam u x *
      ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2) := by
  have hm := (hS.ac_out u u v huv hseg).2.1
  have heq := integralForm_of_ac_of_interior_deriv huv hm
    (fun x hx => IsSolution.hasDerivAt_mass_out hS hseg hx)
  have halg x (hx : x ∈ uIcc u v) :
      S.lam u x * ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 +
        S.Q u x ^ 2 / S.r u x ^ 2) = 2 * S.mV u x := by
    have hx' : x ∈ Icc u v := by simpa only [uIcc_of_le huv] using hx
    have hl := (hS.lam_pos (u, x) (hseg ⟨rfl, hx'⟩)).ne'
    have h := RelCharge.radial_mass_equation hS (hseg ⟨rfl, hx'⟩)
    simpa only [mul_comm] using ((div_eq_iff hl).mp h).symm
  rw [intervalIntegral.integral_congr halg, intervalIntegral.integral_const_mul, ← heq.2]
  simp [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).2.1]


/-- The outgoing mass ratio is the positive radial average of its constraint
density. This exact identity also holds at the axis with total division. -/
private theorem outgoing_mass_ratio_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    S.mu u v = (S.r u v)⁻¹ * ∫ x in u..v, S.lam u x *
      ((1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2 + S.Q u x ^ 2 / S.r u x ^ 2) := by
  rw [Fields.mu, outgoing_mass_reconstruction hS huv hseg]
  ring


/-- The incoming mass ratio uses the density in the same incoming orientation,
with its zero-axis endpoint. The identity has no estimate constants. -/
private theorem incoming_mass_ratio_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) :
    S.mu u v = (S.r u v)⁻¹ * ∫ x in u..v, (-S.nu x v) *
      ((1 - S.mu x v) * ‖S.xi x v / S.nu x v‖ ^ 2 + S.Q x v ^ 2 / S.r x v ^ 2) := by
  rw [Fields.mu, stab_incoming_mass hS huv hseg]
  ring


/-- The complete outgoing radius is exactly the integral of its positive
expansion, including the zero-length segment. -/
private theorem outgoing_radius_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    (∫ x in u..v, S.lam u x) = S.r u v := by
  simpa using outgoing_radius_moment hS huv hseg 0


/-- The incoming radius equation is an ordinary derivative in the interior of
a complete incoming segment in the frozen class. -/
private theorem hasDerivAt_radius_in {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (hseg : inSeg u v v ⊆ D)
    (hx : x ∈ Ioo u v) : HasDerivAt (fun y => S.r y v) (S.nu x v) x := by
  apply hasDerivAt_of_integralForm_interior hx
    ((continuousOn_in_section hS.cont_nu hseg).mono Ioo_subset_Icc_self)
  intro a b ha hab hb
  exact (hS.eq_in a b v hab hb (by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact hseg ⟨ha.le.trans hp₁, hp₂.trans hb.le, rfl⟩)).1

/-- Exact incoming polynomial moments in the original null labels, with
Jacobian `-ν`. The coefficient is `1/(n+1)` uniformly in the solution and
segment. In particular `n=0` reconstructs the incoming radius. -/
theorem incoming_radius_moment_of_solution {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) (n : ℕ) :
    (∫ x in u..v, (-S.nu x v) * S.r x v ^ n) = S.r u v ^ (n + 1) / (n + 1) := by
  have cr := continuousOn_in_section hS.cont_r hseg
  have cn := continuousOn_in_section hS.cont_nu hseg
  have hd : ∀ x ∈ Ioo u v, HasDerivAt
      (fun x => -(S.r x v ^ (n + 1) / (n + 1)))
      ((-S.nu x v) * S.r x v ^ n) x := by
    intro x hx
    convert (((hasDerivAt_radius_in hS hseg hx).pow (n + 1)).div_const
      (n + 1 : ℝ)).neg using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi : IntervalIntegrable (fun x => (-S.nu x v) * S.r x v ^ n) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv (cn.neg.mul (cr.pow n))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((cr.pow (n + 1)).div_const _).neg) hd hi
  simpa [(hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).1] using hftc


/-- The incoming radius is the integral of `-ν` from the point to its axis
endpoint. This exact identity has no estimate constants. -/
private theorem incoming_radius_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) : (∫ x in u..v, -S.nu x v) = S.r u v := by
  simpa using incoming_radius_moment_of_solution hS huv hseg 0


private theorem continuous_constraint_densities {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) :
    ContinuousOn (fun p : ℝ × ℝ => (1 - S.mu p.1 p.2) *
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ^ 2 + S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2)
      (triangle 0 T) ∧
    ContinuousOn (fun p : ℝ × ℝ => (1 - S.mu p.1 p.2) *
      ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ^ 2 + S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2)
      (triangle 0 T) := by
  obtain ⟨q, cq, hq, hqa⟩ := exists_continuous_charge_ratio_aux hset.pos hset.c1
  have cqr : ContinuousOn (fun p : ℝ × ℝ => S.Q p.1 p.2 / S.r p.1 p.2)
      (triangle 0 T) := by
    apply cq.congr
    rintro ⟨u, v⟩ hp
    rcases eq_or_lt_of_le hp.2.1 with huv | huv
    · change u = v at huv
      subst v
      rw [hqa u ⟨hp.1, hp.2.2⟩]
      change S.Q u u / S.r u u = 0
      rw [(hset.c1.axis u hp).1, div_zero]
    · exact (hq u v hp huv).symm
  have cH := (continuousOn_const (c := (1 : ℝ))).sub
    (continuousOn_mu_aux hset.pos hset.c1)
  have cy := hset.c1.c1_theta.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_lam.continuousOn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos p hp).ne')
  have cz := hset.c1.c1_xi.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_nu.continuousOn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg p hp).ne)
  constructor
  · apply ((cH.mul (cy.norm.pow 2)).add (cqr.pow 2)).congr
    intro p _hp
    change (1 - S.mu p.1 p.2) * ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ^ 2 +
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 =
      (1 - S.mu p.1 p.2) * ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ^ 2 +
        (S.Q p.1 p.2 / S.r p.1 p.2) ^ 2
    rw [div_pow]
  · apply ((cH.mul (cz.norm.pow 2)).add (cqr.pow 2)).congr
    intro p _hp
    change (1 - S.mu p.1 p.2) * ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ^ 2 +
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 =
      (1 - S.mu p.1 p.2) * ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ^ 2 +
        (S.Q p.1 p.2 / S.r p.1 p.2) ^ 2
    rw [div_pow]

/-- Before closing the scalar budgets, each oriented weighted mass integral
is bounded by its matching quadratic scalar integral plus
`2 e² M² ε² r(endpoint)²`. These exact coefficients are universal in the
box and independent of higher derivatives. Integrability is a conclusion. -/
theorem AprioriSetting.weighted_mass_preclosure {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (IntervalIntegrable (fun x => S.lam u x / S.r u x * S.mu u x) volume u v ∧
      (∫ x in u..v, S.lam u x / S.r u x * S.mu u x) ≤
        (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) +
          2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) ∧
    (IntervalIntegrable (fun x => -S.nu x v / S.r x v * S.mu x v) volume u v ∧
      (∫ x in u..v, -S.nu x v / S.r x v * S.mu x v) ≤
        (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) +
          2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) := by
  have hS := hset.c1.toIsSolution hset.pos
  let B := 4 * e ^ 2 * M ^ 2 * ε ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let FO := fun a b => (1 - S.mu a b) * ‖S.theta a b / S.lam a b‖ ^ 2 +
    S.Q a b ^ 2 / S.r a b ^ 2
  let FI := fun a b => (1 - S.mu a b) * ‖S.xi a b / S.nu a b‖ ^ 2 +
    S.Q a b ^ 2 / S.r a b ^ 2
  have cF := continuous_constraint_densities hset
  have hFO (a b : ℝ) (hp : (a, b) ∈ triangle 0 T) :
      0 ≤ FO a b ∧ FO a b ≤ ‖S.theta a b / S.lam a b‖ ^ 2 + B * S.r a b ^ 2 := by
    constructor
    · exact add_nonneg (mul_nonneg (hset.c1.one_sub_mu_pos (a, b) hp).le (sq_nonneg _))
        (div_nonneg (sq_nonneg _) (sq_nonneg _))
    · have hi := mul_le_mul_of_nonneg_right
        (sub_le_self (1 : ℝ) (hset.mu_nonneg hp)) (sq_nonneg ‖S.theta a b / S.lam a b‖)
      have hq := hset.charge_sq_div_le hp
      dsimp only [FO, B]
      nlinarith only [hi, hq]
  have hFI (a b : ℝ) (hp : (a, b) ∈ triangle 0 T) :
      0 ≤ FI a b ∧ FI a b ≤ ‖S.xi a b / S.nu a b‖ ^ 2 + B * S.r a b ^ 2 := by
    constructor
    · exact add_nonneg (mul_nonneg (hset.c1.one_sub_mu_pos (a, b) hp).le (sq_nonneg _))
        (div_nonneg (sq_nonneg _) (sq_nonneg _))
    · have hi := mul_le_mul_of_nonneg_right
        (sub_le_self (1 : ℝ) (hset.mu_nonneg hp)) (sq_nonneg ‖S.xi a b / S.nu a b‖)
      have hq := hset.charge_sq_div_le hp
      dsimp only [FI, B]
      nlinarith only [hi, hq]
  have so : outSeg u u v ⊆ triangle 0 T := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu, hx.1, hx.2.trans hvT⟩
  have si : inSeg u v v ⊆ triangle 0 T := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨hu.trans hx, hy, hvT⟩
  have ho (x : ℝ) (hx : x ∈ Icc u v) : (u, x) ∈ triangle 0 T := so ⟨rfl, hx⟩
  have hi (x : ℝ) (hx : x ∈ Icc u v) : (x, v) ∈ triangle 0 T := si ⟨hx.1, hx.2, rfl⟩
  have hquad := hset.quadratic_scalar_integrable hu huv hvT
  constructor
  · have cw := continuousOn_out_section hS.cont_lam so
    have cr := continuousOn_out_section hS.cont_r so
    have cFO : ContinuousOn (fun x => FO u x) (Icc u v) :=
      cF.1.comp (f := fun x : ℝ => (u, x))
        (continuous_const.prodMk continuous_id).continuousOn ho
    have hresult := weighted_mass_of_constraint_density huv hB cw cr cFO
      (fun x hx => (hS.lam_pos (u, x) (ho x hx)).le)
      (fun x hx => hset.radius_nonneg (ho x hx))
      (fun x hx => (outgoing_radius_reconstruction hS hx.1 (by
        rintro p ⟨rfl, hy⟩
        exact ⟨hu, hy.1, hy.2.trans (hx.2.trans hvT)⟩)).symm)
      (fun x hx => hS.r_pos (u, x) (ho x ⟨hx.1.le, hx.2⟩) hx.1)
      (fun x hx => (hFO u x (ho x hx)).1)
      (fun x hx => (hFO u x (ho x hx)).2)
      (fun x hx => outgoing_mass_ratio_reconstruction hS hx.1 (by
        rintro p ⟨rfl, hy⟩
        exact ⟨hu, hy.1, hy.2.trans (hx.2.trans hvT)⟩))
      hquad.1
      (by simpa only [pow_one, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd,
          one_add_one_eq_two] using
        outgoing_radius_moment hS huv so 1)
    refine ⟨hresult.1, ?_⟩
    have hb := hresult.2
    have hcoef : B * S.r u v ^ 2 / 2 =
        2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by dsimp only [B]; ring
    rwa [hcoef] at hb
  · have hneg : MapsTo (fun x : ℝ => -x) (Icc (-v) (-u)) (Icc u v) := by
      intro x hx
      constructor <;> linarith only [hx.1, hx.2]
    have hm (x : ℝ) (hx : x ∈ Icc (-v) (-u)) : (-x, v) ∈ triangle 0 T := hi (-x) (hneg hx)
    have sx (x : ℝ) (hx : x ∈ Icc (-v) (-u)) : inSeg (-x) v v ⊆ triangle 0 T := by
      rintro p ⟨ha, hb, rfl⟩
      exact ⟨(hm x hx).1.trans ha, hb, hvT⟩
    have cw : ContinuousOn (fun x => -S.nu (-x) v) (Icc (-v) (-u)) :=
      (continuousOn_in_section hS.cont_nu si).neg.comp continuous_neg.continuousOn hneg
    have cr : ContinuousOn (fun x => S.r (-x) v) (Icc (-v) (-u)) :=
      (continuousOn_in_section hS.cont_r si).comp continuous_neg.continuousOn hneg
    have cFI : ContinuousOn (fun x => FI (-x) v) (Icc (-v) (-u)) :=
      cF.2.comp (f := fun x : ℝ => (-x, v))
        (continuous_neg.prodMk continuous_const).continuousOn hm
    have hresult := weighted_mass_of_constraint_density (μ := fun x => S.mu (-x) v)
      (z := fun x => S.xi (-x) v / S.nu (-x) v) (neg_le_neg huv) hB cw cr cFI
      (fun x hx => (neg_pos.mpr (hS.nu_neg (-x, v) (hm x hx))).le)
      (fun x hx => hset.radius_nonneg (hm x hx))
      (fun x hx => by
        rw [intervalIntegral.integral_comp_neg (f := fun y => -S.nu y v)]
        simpa only [neg_neg] using (incoming_radius_reconstruction hS (hneg hx).2 (sx x hx)).symm)
      (fun x hx => hS.r_pos (-x, v) (hm x ⟨hx.1.le, hx.2⟩) (by linarith only [hx.1]))
      (fun x hx => (hFI (-x) v (hm x hx)).1)
      (fun x hx => (hFI (-x) v (hm x hx)).2)
      (fun x hx => by
        rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) * FI y v)]
        simpa only [neg_neg] using incoming_mass_ratio_reconstruction hS (hneg hx).2 (sx x hx))
      (((IntervalIntegrable.iff_comp_neg).mp hquad.2).symm)
      (by
        rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) * S.r y v)]
        simpa only [neg_neg, pow_one, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd,
          one_add_one_eq_two] using
          incoming_radius_moment_of_solution hS huv si 1)
    have iresult : IntervalIntegrable (fun x => -S.nu x v / S.r x v * S.mu x v) volume u v :=
      (IntervalIntegrable.iff_comp_neg).mpr hresult.1.symm
    refine ⟨iresult, ?_⟩
    have hb := hresult.2
    rw [intervalIntegral.integral_comp_neg (f := fun x => -S.nu x v / S.r x v * S.mu x v),
      intervalIntegral.integral_comp_neg (f := fun x =>
        -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2)] at hb
    simp only [neg_neg] at hb
    have hcoef : B * S.r u v ^ 2 / 2 =
        2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by dsimp only [B]; ring
    rwa [hcoef] at hb

/-- [node restart-sec-independent-area#weighted-mass-budgets]
The weighted ordinary mass integrals in both characteristic orientations
are bounded by `C ε² (1 + (|e| R M)²)` on every complete axis-to-point segment.
The thresholds and `C` precede all data and depend only on the fixed box,
uniformly in higher initial derivatives. The implemented coefficient is `14`.
The nonnegative-integral statement also certifies finiteness at the axis. -/
theorem weighted_mass_budgets : ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      (∫⁻ x in Icc u v, ENNReal.ofReal (S.lam u x / S.r u x * S.mu u x)) ≤
          ENNReal.ofReal (C * ε ^ 2 * (1 + (|e| * (T / 2) * M) ^ 2)) ∧
      (∫⁻ x in Icc u v, ENNReal.ofReal (-S.nu x v / S.r x v * S.mu x v)) ≤
          ENNReal.ofReal (C * ε ^ 2 * (1 + (|e| * (T / 2) * M) ^ 2)) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hflux⟩ := closed_quadratic_scalar_budgets
  refine ⟨ε₀, δ₀, 14, hε₀, hδ₀, by norm_num, ?_⟩
  intro e T ε M S h hset hε hδ u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  have hmass := hset.weighted_mass_preclosure hu huv hvT
  have hquad := hflux e T ε M S h hset hε hδ u v hu huv hvT
  have hr0 := hset.radius_nonneg hp
  have hrT : S.r u v ≤ T := (Area.radius_bounds hset hu huv hvT).2.trans
    (by linarith only [hu, hvT])
  have hcharge : 2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 ≤
      8 * (|e| * (T / 2) * M) ^ 2 * ε ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2)
      (show 0 ≤ 2 * e ^ 2 * M ^ 2 * ε ^ 2 by positivity)
    convert hi using 1
    simp only [mul_pow, sq_abs]
    ring
  have ho := hmass.1.2.trans (add_le_add hquad.1 hcharge)
  have hi := hmass.2.2.trans (add_le_add hquad.2 hcharge)
  have hout : (∫ x in u..v, S.lam u x / S.r u x * S.mu u x) ≤
      14 * ε ^ 2 * (1 + (|e| * (T / 2) * M) ^ 2) := by
    nlinarith only [ho, mul_nonneg (sq_nonneg (|e| * (T / 2) * M)) (sq_nonneg ε)]
  have hin : (∫ x in u..v, -S.nu x v / S.r x v * S.mu x v) ≤
      14 * ε ^ 2 * (1 + (|e| * (T / 2) * M) ^ 2) := by
    nlinarith only [hi, mul_nonneg (sq_nonneg (|e| * (T / 2) * M)) (sq_nonneg ε)]
  constructor
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hmass.1.1)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hp' : (u, x) ∈ triangle 0 T := ⟨hu, hx.1, hx.2.trans hvT⟩
        exact mul_nonneg (div_nonneg (hset.c1.lam_pos (u, x) hp').le
          (hset.radius_nonneg hp')) (hset.mu_nonneg hp')),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
    exact ENNReal.ofReal_le_ofReal hout
  · rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mp hmass.2.1)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hp' : (x, v) ∈ triangle 0 T := ⟨hu.trans hx.1, hx.2, hvT⟩
        exact mul_nonneg (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, v) hp')).le
          (hset.radius_nonneg hp')) (hset.mu_nonneg hp')),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv]
    exact ENNReal.ofReal_le_ofReal hin

end EmcsfAcExtension.Local
