module

public import EmcsfAcExtension.Local.Broad.GeometryCone

/-! # Endpoint uniqueness for the entering-cone constraints

Continuous zero-axis masses are compared by a dissipative square. This
avoids assuming integrability of an integrating-factor coefficient at the
axis. All derivative statements concern open characteristic sections.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- A continuous function with zero interior derivative is constant up to both
endpoints. The assertion is valid for real or complex fields and has no
estimate constants. -/
theorem eq_endpoint_of_hasDerivAt_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} {f : ℝ → E}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f b = f a := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf hd
    (intervalIntegrable_const (c := (0 : E)))
  simpa only [intervalIntegral.integral_zero, eq_comm, sub_eq_zero] using hi

/-- A nonnegative damping coefficient gives uniqueness from the zero initial
value, even if it is singular at the initial endpoint. Only continuity of
the unknown and its ordinary interior equation are used. -/
theorem eq_zero_of_damped_derivative {a b : ℝ} {f k : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hzero : f a = 0)
    (hk : ∀ x ∈ Ioo a b, 0 ≤ k x)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (-k x * f x) x) : f b = 0 := by
  have hanti : AntitoneOn (fun x => f x ^ 2) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) (hf.pow 2)
    · intro x hx
      rw [interior_Icc] at hx
      exact ((hd x hx).pow 2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [((hd x hx).pow 2).deriv]
      norm_num only [Nat.reduceSub, pow_one]
      have hn := mul_nonneg (hk x hx) (sq_nonneg (f x))
      nlinarith only [hn]
  have hle := hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  change f b ^ 2 ≤ f a ^ 2 at hle
  rw [hzero, zero_pow (by decide : 2 ≠ 0)] at hle
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))

/-- Equal radius, expansion, outgoing transport field and charge determine
the ordinary mass on a complete cone. No smallness, variation or envelope
bound is needed. -/
theorem cone_mass_eq_of_constraint_fields_eq {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u ≤ v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hr : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x)
    (hl : ∀ x ∈ Icc u v, S₁.lam u x = S₂.lam u x)
    (ht : ∀ x ∈ Icc u v, S₁.theta u x = S₂.theta u x)
    (hq : ∀ x ∈ Icc u v, S₁.Q u x = S₂.Q u x) : S₁.m u v = S₂.m u v := by
  apply sub_eq_zero.mp
  apply eq_zero_of_damped_derivative huv
    ((continuousOn_out_section hS₁.cont_m hs₁).sub
      (continuousOn_out_section hS₂.cont_m hs₂))
    (by simp [(hS₁.axis u (hs₁ ⟨rfl, le_rfl, huv⟩)).2.1,
      (hS₂.axis u (hs₂ ⟨rfl, le_rfl, huv⟩)).2.1])
    (k := fun x => ‖S₂.theta u x‖ ^ 2 / (S₂.r u x * S₂.lam u x))
  · intro x hx
    exact div_nonneg (sq_nonneg _) (mul_nonneg
      (hS₂.r_pos (u, x) (hs₂ ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).le
      (hS₂.lam_pos (u, x) (hs₂ ⟨rfl, hx.1.le, hx.2.le⟩)).le)
  · intro x hx
    apply ((IsSolution.hasDerivAt_mass_out hS₁ hs₁ hx).sub
      (IsSolution.hasDerivAt_mass_out hS₂ hs₂ hx)).congr_deriv
    have hx' : x ∈ Icc u v := Ioo_subset_Icc_self hx
    have hr0 := (hS₂.r_pos (u, x) (hs₂ ⟨rfl, hx'⟩) hx.1).ne'
    have hl0 := (hS₂.lam_pos (u, x) (hs₂ ⟨rfl, hx'⟩)).ne'
    simp only [Fields.mV, Fields.mu, hr x hx', hl x hx', ht x hx', hq x hx', Pi.sub_apply]
    field_simp [hr0, hl0]
    ring

/-- The incoming expansion has its prescribed ordinary outgoing derivative
in the open part of a complete cone, directly in the broad integral class. -/
theorem hasDerivAt_nu_out {e u v x : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hs : outSeg u u v ⊆ D) (hx : x ∈ Ioo u v) :
    HasDerivAt (S.nu u) (S.rUV u x) x := by
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) D) :=
    (continuousOn_out_section hf hs).mono Ioo_subset_Icc_self
  have cr := sect hS.cont_r
  have cm := sect hS.cont_m
  have cl := sect hS.cont_lam
  have cn := sect hS.cont_nu
  have cq := sect hS.cont_Q
  have nr : ∀ y ∈ Ioo u v, S.r u y ≠ 0 := fun y hy =>
    (hS.r_pos (u, y) (hs ⟨rfl, hy.1.le, hy.2.le⟩) hy.1).ne'
  have cμ : ContinuousOn (S.mu u) (Ioo u v) := (continuousOn_const.mul cm).div cr nr
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Ioo u v) := continuousOn_const.sub cμ
  have ng : ∀ y ∈ Ioo u v, 1 - S.mu u y ≠ 0 := fun y hy =>
    (hS.one_sub_mu_pos (u, y) (hs ⟨rfl, hy.1.le, hy.2.le⟩)).ne'
  have csource : ContinuousOn (S.rUV u) (Ioo u v) :=
    ((cn.mul cl).div cr nr).mul
      ((cμ.sub ((cq.pow 2).div (cr.pow 2) (fun y hy => pow_ne_zero 2 (nr y hy)))).div cg ng)
  apply hasDerivAt_of_integralForm_interior hx csource
  intro c d hc hcd hd
  exact (hS.eq_out u c d hc hcd (by
    rintro p ⟨rfl, hp⟩
    exact hs ⟨rfl, hc.le.trans hp.1, hp.2.trans hd.le⟩)).2.1

/-- Once radius, outgoing expansion, mass and charge agree, the common
axis value determines the incoming expansion. The ratio argument requires
no integrability assertion at the singular endpoint. -/
theorem cone_nu_eq_of_constraint_fields_eq {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u ≤ v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hr : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x)
    (hl : ∀ x ∈ Icc u v, S₁.lam u x = S₂.lam u x)
    (hm : ∀ x ∈ Icc u v, S₁.m u x = S₂.m u x)
    (hq : ∀ x ∈ Icc u v, S₁.Q u x = S₂.Q u x) : S₁.nu u v = S₂.nu u v := by
  have hnz x (hx : x ∈ Icc u v) : S₂.nu u x ≠ 0 :=
    (hS₂.nu_neg (u, x) (hs₂ ⟨rfl, hx⟩)).ne
  have hc : ContinuousOn (fun x => S₁.nu u x / S₂.nu u x) (Icc u v) :=
    (continuousOn_out_section hS₁.cont_nu hs₁).div
      (continuousOn_out_section hS₂.cont_nu hs₂) hnz
  have hd x (hx : x ∈ Ioo u v) : HasDerivAt
      (fun x => S₁.nu u x / S₂.nu u x) 0 x := by
    apply ((hasDerivAt_nu_out hS₁ hs₁ hx).div
      (hasDerivAt_nu_out hS₂ hs₂ hx) (hnz x (Ioo_subset_Icc_self hx))).congr_deriv
    simp only [Fields.rUV, Fields.mu, hr x (Ioo_subset_Icc_self hx),
      hl x (Ioo_subset_Icc_self hx), hm x (Ioo_subset_Icc_self hx),
      hq x (Ioo_subset_Icc_self hx)]
    ring
  have hratio := eq_endpoint_of_hasDerivAt_zero huv hc hd
  have haxis₁ := (hS₁.axis u (hs₁ ⟨rfl, le_rfl, huv⟩)).2.2.2.1
  have haxis₂ := (hS₂.axis u (hs₂ ⟨rfl, le_rfl, huv⟩)).2.2.2.1
  have haxis : S₁.nu u u = S₂.nu u u := by
    linarith [hl u ⟨le_rfl, huv⟩]
  rw [haxis, div_self (hnz u ⟨le_rfl, huv⟩)] at hratio
  exact (div_eq_one_iff_eq (hnz v ⟨huv, le_rfl⟩)).mp hratio

/-- Equal off-axis primitive increments and equal vertex values determine
continuous fields on the complete cone. This permits endpoint constraint
uniqueness without an extra AC hypothesis on the field. -/
theorem eq_endpoint_of_equal_increments {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f g : ℝ → E} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hzero : f a = g a)
    (hinc : ∀ c d, a < c → c ≤ d → d < b → f d - f c = g d - g c) : f b = g b := by
  let z := (a + b) / 2
  have hz : z ∈ Ioo a b := ⟨by dsimp [z]; linarith, by dsimp [z]; linarith⟩
  have heq : EqOn (fun x => f x - g x) (fun _ => f z - g z) (Ioo a b) := by
    intro x hx
    rcases le_total x z with h | h
    · have hi := hinc x z hx.1 h hz.2
      calc
        f x - g x = f z - g z - ((f z - f x) - (g z - g x)) := by abel
        _ = f z - g z := by rw [hi, sub_self, sub_zero]
    · have hi := hinc z x hz.1 h hx.2
      calc
        f x - g x = ((f x - f z) - (g x - g z)) + (f z - g z) := by abel
        _ = f z - g z := by rw [hi, sub_self, zero_add]
  have hall := heq.of_subset_closure (hf.sub hg) continuousOn_const Ioo_subset_Icc_self
    (show Icc a b ⊆ closure (Ioo a b) by rw [closure_Ioo hab.ne])
  have ha := hall ⟨le_rfl, hab.le⟩
  have hb := hall ⟨hab.le, le_rfl⟩
  change f a - g a = f z - g z at ha
  change f b - g b = f z - g z at hb
  rw [hzero, sub_self] at ha
  exact sub_eq_zero.mp (hb.trans ha.symm)

end EmcsfAcExtension.Local.Broad
