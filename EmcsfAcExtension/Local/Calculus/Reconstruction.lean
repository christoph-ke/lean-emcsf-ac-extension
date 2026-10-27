module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Axis-to-point radial reconstruction

The scalar identities in charged_SF_new_version.tex:L4595–4606 and the incoming mass
identity in charged_SF_new_version.tex:L5677–5677. All integrals use the original null
labels; their radial densities include the Jacobians `λ` and `-ν`.
-/

public section

open Set MeasureTheory Filter Complex
open scoped Topology

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recover an ordinary interior derivative from continuous integral equations.
Only equations on compact subintervals of the open interval are required. -/
theorem hasDerivAt_of_integralForm_interior [CompleteSpace E]
    {f g : ℝ → E} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hg : ContinuousOn g (Ioo a b))
    (heq : ∀ c d, a < c → c ≤ d → d < b → IntegralForm f g c d) :
    HasDerivAt f (g x) x := by
  let c := (a + x) / 2
  let d := (x + b) / 2
  have hac : a < c := by dsimp [c]; linarith [hx.1]
  have hcx : c < x := by dsimp [c]; linarith [hx.1]
  have hxd : x < d := by dsimp [d]; linarith [hx.2]
  have hdb : d < b := by dsimp [d]; linarith [hx.2]
  have hcont : ContinuousAt g x := hg.continuousAt (isOpen_Ioo.mem_nhds hx)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (heq c x hac hcx.le hx.2).1
    (hg.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    hcont
  apply (hd.const_add (f c)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hcx hxd] with y hy
  exact (heq c y hac hy.1.le (hy.2.trans hdb)).eq_add_integral

/-- Extend an equation to the axis using the absolute continuity already present
in the frozen class. Endpoint derivative values play no role. -/
theorem integralForm_of_ac_of_interior_deriv [FiniteDimensional ℝ E]
    {f g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) : IntegralForm f g a b := by
  apply integralForm_of_ac_of_ae_deriv_eq hf
  rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc]
  exact (ae_restrict_mem measurableSet_Ioo).mono fun x hx => (hd x hx).deriv

section
omit [NormedSpace ℝ E]

/-- Restrict a continuous field to an outgoing axis-to-point segment. -/
theorem continuousOn_out_section {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)}
    (hf : ContinuousOn (Function.uncurry f) D) {u v : ℝ}
    (hseg : outSeg u u v ⊆ D) : ContinuousOn (f u) (Icc u v) :=
  hf.comp (continuousOn_const.prodMk continuousOn_id) (fun _ hx => hseg ⟨rfl, hx⟩)

/-- Restrict a continuous field to an incoming axis-to-point segment. -/
theorem continuousOn_in_section {f : ℝ → ℝ → E} {D : Set (ℝ × ℝ)}
    (hf : ContinuousOn (Function.uncurry f) D) {u v : ℝ}
    (hseg : inSeg u v v ⊆ D) : ContinuousOn (fun s => f s v) (Icc u v) :=
  hf.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hx => hseg ⟨hx.1, hx.2, rfl⟩)

end

private theorem c1_out_deriv {a b u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (ha : a ≤ u) (huv : u < v) (hvb : v < b) :
    HasDerivAt (f u) (pdV (triangle a b) f u v) v :=
  (hasDerivWithinAt_uncurry_triangle_v hf ⟨ha, huv.le, hvb.le⟩).hasDerivAt
    (Icc_mem_nhds huv hvb)

private theorem c1_in_deriv {a b u v : ℝ} {f : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (ha : a < u) (huv : u < v) (hvb : v ≤ b) :
    HasDerivAt (fun s => f s v) (pdU (triangle a b) f u v) u :=
  (hasDerivWithinAt_uncurry_triangle_u hf ⟨ha.le, huv.le, hvb⟩).hasDerivAt
    (Icc_mem_nhds ha huv)

/-- [node restart-sec-independent-area#outgoing-radial-reconstruction]
Outgoing scalar reconstruction in null labels (`dr = λ dv`),
charged_SF_new_version.tex:L4595–4596. This exact identity has no constants. -/
theorem Area.outgoing_radial_reconstruction {e a b : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) {u v : ℝ}
    (ha : a ≤ u) (huv : u ≤ v) (hb : v ≤ b) :
    (S.r u v : ℂ) * S.phi u v = ∫ s in u..v, (S.lam u s : ℂ) * S.a u s := by
  have hseg : outSeg u u v ⊆ triangle a b := by
    rintro p ⟨rfl, hp⟩
    exact ⟨ha, hp.1, hp.2.trans hb⟩
  have cr := continuousOn_out_section hS.c1_r.continuousOn hseg
  have cp := continuousOn_out_section hS.c1_phi.continuousOn hseg
  have cl := continuousOn_out_section hS.c1_lam.continuousOn hseg
  have ct := continuousOn_out_section hS.c1_theta.continuousOn hseg
  have ca : ContinuousOn (S.a u) (Icc u v) :=
    cp.add (ct.div (continuous_ofReal.comp_continuousOn cl) (fun s hs => by
      exact_mod_cast (hS.lam_pos (u, s) (hseg ⟨rfl, hs⟩)).ne'))
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    ((continuous_ofReal.comp_continuousOn cl).mul ca)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((continuous_ofReal.comp_continuousOn cr).mul cp)
    (f' := fun s => (S.lam u s : ℂ) * S.a u s) (fun s hs => ?_) hi
  · simpa [hS.axis u ⟨ha, le_rfl, huv.trans hb⟩ |>.1] using hftc.symm
  · have he := hS.eq_v (u, s) ⟨ha, hs.1.le, hs.2.le.trans hb⟩ hs.1
    have hr := c1_out_deriv hS.c1_r ha hs.1 (hs.2.trans_le hb)
    have hp := c1_out_deriv hS.c1_phi ha hs.1 (hs.2.trans_le hb)
    rw [he.1] at hr
    rw [he.2.2.2.2.2.1] at hp
    have hrC : (S.r u s : ℂ) ≠ 0 := by
      exact_mod_cast (hS.r_pos (u, s) ⟨ha, hs.1.le, hs.2.le.trans hb⟩ hs.1).ne'
    have hlC : (S.lam u s : ℂ) ≠ 0 := by
      exact_mod_cast (hS.lam_pos (u, s) ⟨ha, hs.1.le, hs.2.le.trans hb⟩).ne'
    apply (hr.ofReal_comp.mul hp).congr_deriv
    dsimp [Fields.a, Fields.phiV]
    field_simp [hrC, hlC]

/-- [node restart-sec-independent-area#incoming-parallel-reconstruction]
The incoming integrating factor is unitary. Its basepoint is arbitrary, and
there are no constants or bounds on the real connection. -/
theorem Area.incoming_parallel_factor_norm (e c s v : ℝ) (S : Fields) :
    ‖Complex.exp (I * e * (∫ t in c..s, S.A t v : ℝ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- [node restart-sec-independent-area#incoming-parallel-reconstruction]
Incoming scalar reconstruction in the unitary frame based at the endpoint
`u`, charged_SF_new_version.tex:L4604–4606. The Jacobian `-ν` makes the integral positive
from the endpoint towards the axis. This is an exact identity. -/
theorem Area.incoming_parallel_reconstruction {e a b : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) {u v : ℝ}
    (ha : a ≤ u) (huv : u ≤ v) (hb : v ≤ b) :
    (S.r u v : ℂ) * S.phi u v = ∫ s in u..v,
      (-S.nu s v : ℂ) * Complex.exp (I * e * (∫ t in u..s, S.A t v : ℝ)) * S.b s v := by
  have hseg : inSeg u v v ⊆ triangle a b := by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact ⟨ha.trans hp₁, hp₂, hb⟩
  have cr := continuousOn_in_section hS.c1_r.continuousOn hseg
  have cp := continuousOn_in_section hS.c1_phi.continuousOn hseg
  have cn := continuousOn_in_section hS.c1_nu.continuousOn hseg
  have cx := continuousOn_in_section hS.c1_xi.continuousOn hseg
  have cA := continuousOn_in_section hS.c1_A.continuousOn hseg
  have cb : ContinuousOn (fun s => S.b s v) (Icc u v) :=
    cp.add (cx.div (continuous_ofReal.comp_continuousOn cn) (fun s hs => by
      exact_mod_cast (hS.nu_neg (s, v) (hseg ⟨hs.1, hs.2, rfl⟩)).ne))
  have iA := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cA
  have cI := iA.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc |>.continuousOn
  rw [uIcc_of_le huv] at cI
  let P := fun s => Complex.exp (I * e * (∫ t in u..s, S.A t v : ℝ))
  have cP : ContinuousOn P (Icc u v) := Complex.continuous_exp.comp_continuousOn
    ((continuousOn_const.mul continuousOn_const).mul (continuous_ofReal.comp_continuousOn cI))
  have hd : ∀ s ∈ Ioo u v, HasDerivAt
      (fun x => (S.r x v : ℂ) * P x * S.phi x v)
      ((S.nu s v : ℂ) * P s * S.b s v) s := by
    intro s hs
    have he := hS.eq_u (s, v) ⟨ha.trans hs.1.le, hs.2.le, hb⟩ hs.2
    have hr := c1_in_deriv hS.c1_r (ha.trans_lt hs.1) hs.2 hb
    have hp := c1_in_deriv hS.c1_phi (ha.trans_lt hs.1) hs.2 hb
    rw [he.1] at hr
    rw [he.2.2.2.2.1] at hp
    have cAo := cA.mono Ioo_subset_Icc_self
    have hI := intervalIntegral.integral_hasDerivAt_right
      (iA.mono_set (by
        rw [uIcc_of_le hs.1.le, uIcc_of_le huv]
        exact Icc_subset_Icc le_rfl hs.2.le))
      (cAo.stronglyMeasurableAtFilter isOpen_Ioo s hs)
      (cAo.continuousAt (isOpen_Ioo.mem_nhds hs))
    have hP := (hI.ofReal_comp.const_mul (I * (e : ℂ))).cexp
    have hrC : (S.r s v : ℂ) ≠ 0 := by
      exact_mod_cast (hS.r_pos (s, v) ⟨ha.trans hs.1.le, hs.2.le, hb⟩ hs.2).ne'
    have hnC : (S.nu s v : ℂ) ≠ 0 := by
      exact_mod_cast (hS.nu_neg (s, v) ⟨ha.trans hs.1.le, hs.2.le, hb⟩).ne
    apply ((hr.ofReal_comp.mul hP).mul hp).congr_deriv
    dsimp [Fields.b, Fields.phiU, P]
    field_simp [hrC, hnC]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((continuous_ofReal.comp_continuousOn cr).mul cP).mul cp) hd
    (show IntervalIntegrable (fun s => (S.nu s v : ℂ) * P s * S.b s v) volume u v from
      ContinuousOn.intervalIntegrable_of_Icc huv
        (((continuous_ofReal.comp_continuousOn cn).mul cP).mul cb))
  have hneg : (∫ s in u..v, (-S.nu s v : ℂ) * P s * S.b s v) =
      -(∫ s in u..v, (S.nu s v : ℂ) * P s * S.b s v) := by
    simp only [neg_mul, intervalIntegral.integral_neg]
  rw [hneg, hftc]
  simp [P, (hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).1]

/-- The outgoing radius equation holds as an ordinary derivative in the interior
of every outgoing segment in the broad AC class. -/
theorem IsSolution.hasDerivAt_radius_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (hseg : outSeg u u v ⊆ D)
    (hs : s ∈ Ioo u v) : HasDerivAt (S.r u) (S.lam u s) s := by
  apply hasDerivAt_of_integralForm_interior hs
    ((continuousOn_out_section hS.cont_lam hseg).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (by
    rintro p ⟨rfl, hp⟩
    exact hseg ⟨rfl, hc.le.trans hp.1, hp.2.trans hd.le⟩)).1

/-- The outgoing Maxwell equation is an ordinary interior derivative even for a
solution in the broad AC class. -/
theorem IsSolution.hasDerivAt_charge_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (hseg : outSeg u u v ⊆ D)
    (hs : s ∈ Ioo u v) : HasDerivAt (S.Q u) (S.QV e u s) s := by
  have cr := continuousOn_out_section hS.cont_r hseg
  have cp := continuousOn_out_section hS.cont_phi hseg
  have ct := continuousOn_out_section hS.cont_theta hseg
  apply hasDerivAt_of_integralForm_interior hs
    (((continuousOn_const.mul cr).mul
      (continuous_im.comp_continuousOn (cp.star.mul ct))).neg.mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (by
    rintro p ⟨rfl, hp⟩
    exact hseg ⟨rfl, hc.le.trans hp.1, hp.2.trans hd.le⟩)).2.2.2.1

/-- The incoming mass equation is an ordinary interior derivative in the broad
AC class. No renormalized derivative or envelope is assumed. -/
theorem IsSolution.hasDerivAt_mass_in {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (hseg : inSeg u v v ⊆ D)
    (hs : s ∈ Ioo u v) : HasDerivAt (fun x => S.m x v) (S.mU s v) s := by
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) D) :=
    (continuousOn_in_section hf hseg).mono Ioo_subset_Icc_self
  have cr := sect hS.cont_r
  have cm := sect hS.cont_m
  have cq := sect hS.cont_Q
  have cn := sect hS.cont_nu
  have cx := (continuousOn_in_section hS.cont_xi hseg).mono Ioo_subset_Icc_self
  have nr : ∀ x ∈ Ioo u v, S.r x v ≠ 0 := fun x hx =>
    (hS.r_pos (x, v) (hseg ⟨hx.1.le, hx.2.le, rfl⟩) hx.2).ne'
  have nn : ∀ x ∈ Ioo u v, 2 * S.nu x v ≠ 0 := fun x hx =>
    mul_ne_zero (by norm_num) (hS.nu_neg (x, v) (hseg ⟨hx.1.le, hx.2.le, rfl⟩)).ne
  have cg : ContinuousOn (fun x => 1 - S.mu x v) (Ioo u v) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cg' : ContinuousOn (fun x => S.mU x v) (Ioo u v) :=
    ((cg.mul (cx.norm.pow 2)).div (continuousOn_const.mul cn) nn).add
      (((cq.pow 2).mul cn).div (continuousOn_const.mul (cr.pow 2))
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero _ (nr x hx))))
  apply hasDerivAt_of_integralForm_interior hs cg'
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd hd (by
    rintro p ⟨hp₁, hp₂, rfl⟩
    exact hseg ⟨hc.le.trans hp₁, hp₂.trans hd.le, rfl⟩)).2.2.1

/-- The outgoing mass equation is an ordinary interior derivative in the broad
AC class. This uses only the equations and continuity away from the axis. -/
theorem IsSolution.hasDerivAt_mass_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v s : ℝ} (hseg : outSeg u u v ⊆ D)
    (hs : s ∈ Ioo u v) : HasDerivAt (S.m u) (S.mV u s) s := by
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) D) :=
    (continuousOn_out_section hf hseg).mono Ioo_subset_Icc_self
  have cr := sect hS.cont_r
  have cm := sect hS.cont_m
  have cq := sect hS.cont_Q
  have cl := sect hS.cont_lam
  have ct := (continuousOn_out_section hS.cont_theta hseg).mono Ioo_subset_Icc_self
  have nr : ∀ x ∈ Ioo u v, S.r u x ≠ 0 := fun x hx =>
    (hS.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne'
  have nl : ∀ x ∈ Ioo u v, 2 * S.lam u x ≠ 0 := fun x hx =>
    mul_ne_zero (by norm_num) (hS.lam_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2.le⟩)).ne'
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Ioo u v) :=
    continuousOn_const.sub ((continuousOn_const.mul cm).div cr nr)
  have cg' : ContinuousOn (S.mV u) (Ioo u v) :=
    ((cg.mul (ct.norm.pow 2)).div (continuousOn_const.mul cl) nl).add
      (((cq.pow 2).mul cl).div (continuousOn_const.mul (cr.pow 2))
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero _ (nr x hx))))
  apply hasDerivAt_of_integralForm_interior hs cg'
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (by
    rintro p ⟨rfl, hp⟩
    exact hseg ⟨rfl, hc.le.trans hp.1, hp.2.trans hd.le⟩)).2.2.1

/-- Exact radial moments in the original outgoing labels. For every natural
`n`, the coefficient is precisely `1 / (n+1)`, independently of the solution. -/
theorem outgoing_radius_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (n : ℕ) :
    (∫ s in u..v, S.lam u s * S.r u s ^ n) = S.r u v ^ (n + 1) / (n + 1) := by
  have cr := continuousOn_out_section hS.cont_r hseg
  have cl := continuousOn_out_section hS.cont_lam hseg
  have hd : ∀ s ∈ Ioo u v, HasDerivAt
      (fun s => S.r u s ^ (n + 1) / (n + 1)) (S.lam u s * S.r u s ^ n) s := by
    intro s hs
    convert ((IsSolution.hasDerivAt_radius_out hS hseg hs).pow (n + 1)).div_const
      (n + 1 : ℝ) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv (cl.mul (cr.pow n))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((cr.pow (n + 1)).div_const _) hd hi
  simpa [(hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).1] using hftc

/-- [node restart-stab-incoming-mass]
The same-orientation incoming mass representation, charged_SF_new_version.tex:L5677–5677.
It holds in the broad AC class on any complete incoming segment. There are no
constants, geometric box assumptions, or envelope assumptions. -/
theorem stab_incoming_mass {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u ≤ v)
    (hseg : inSeg u v v ⊆ D) :
    2 * S.m u v = ∫ s in u..v, (-S.nu s v) *
      ((1 - S.mu s v) * ‖S.xi s v / S.nu s v‖ ^ 2 + S.Q s v ^ 2 / S.r s v ^ 2) := by
  have hm := (hS.ac_in u v v huv hseg).2.1
  have heq := integralForm_of_ac_of_interior_deriv huv hm
    (fun s hs => IsSolution.hasDerivAt_mass_in hS hseg hs)
  have hi := intervalIntegral.integral_const_mul (a := u) (b := v) (μ := volume)
    (-2 : ℝ) (fun s => S.mU s v)
  have halg : (fun s => -2 * S.mU s v) =ᵐ[volume.restrict (uIoc u v)]
      (fun s => (-S.nu s v) * ((1 - S.mu s v) * ‖S.xi s v / S.nu s v‖ ^ 2 +
        S.Q s v ^ 2 / S.r s v ^ 2)) := by
    rw [uIoc_of_le huv]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hn := (hS.nu_neg (s, v) (hseg ⟨hs.1.le, hs.2, rfl⟩)).ne
    simp only [Fields.mU, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    field_simp [hn]
  rw [← intervalIntegral.integral_congr_ae_restrict halg, hi, ← heq.2]
  simp [(hS.axis v (hseg ⟨huv, le_rfl, rfl⟩)).2.1]

end EmcsfAcExtension.Local
