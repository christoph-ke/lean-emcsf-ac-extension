module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Local.Calculus.Sections

/-! # Incoming connector mass and weighted flux

The clock measure is written in the original incoming label as
`dτ = (-ν) du`. This keeps the exact electric loss in the mass balance and
requires no choice of an inverse clock. Source: `charged_SF_new_version.tex:L3835–L3836`,
approved internal project record, and the ratified reading internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Interaction

private theorem mass_density (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0) :
    ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
      S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v) = -2 * S.mU u v := by
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  dsimp only [Fields.mU]
  field_simp [hr, hn]

/-- [node sec:charged-terminal-interaction#connector-mass-equation]
The incoming mass equation divided by the positive connector clock rate.
The derivative is a.e. on the proper incoming segment; constants: none.
The electric contribution has the dissipative sign. -/
theorem connector_mass_equation {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    ∀ᵐ u ∂volume.restrict (Icc a b),
      deriv (fun x => S.m x v) u / (-S.nu u v) =
        -(1 - S.mu u v) / 2 * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 -
          S.Q u v ^ 2 / (2 * S.r u v ^ 2) := by
  filter_upwards [(Local.IsSolution.in_section hS hab hbv hs).2.2.1.2,
    ae_restrict_mem measurableSet_Icc] with u hu hum
  rw [hu.deriv]
  have hp : (u, v) ∈ D := hs ⟨hum.1, hum.2, rfl⟩
  have hd := mass_density S u v (hS.r_pos _ hp (hum.2.trans_lt hbv)).ne'
    (hS.nu_neg _ hp).ne
  apply (div_eq_iff (neg_ne_zero.mpr (hS.nu_neg _ hp).ne)).2
  linear_combination 1 / 2 * hd

/-- [internal] Exact connector balance at every partial endpoint. All
integrals are in the original label with the clock Jacobian `-ν`.
Constants: the exact coefficient `1/2`, independent of all data. -/
theorem connector_mass_balance {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (_hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    ∀ x ∈ Icc a b,
      S.m x v + (1 / 2 : ℝ) * (∫ u in a..x,
        ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
          S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v)) = S.m a v := by
  intro x hx
  have hsx : inSeg a x v ⊆ D := fun p hp => hs ⟨hp.1, hp.2.1.trans hx.2, hp.2.2⟩
  have hm := (Calculus.in_integralForm hS hx.1 (hx.2.trans hbv.le) hsx).2.2.1
  have he : (∫ u in a..x,
      ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v)) =
      -2 * (∫ u in a..x, S.mU u v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx.1] at hu
    have hp : (u, v) ∈ D := hsx ⟨hu.1, hu.2, rfl⟩
    exact mass_density S u v (hS.r_pos _ hp (hu.2.trans_lt (hx.2.trans_lt hbv))).ne'
      (hS.nu_neg _ hp).ne
  rw [he, ← hm.2]
  ring

private theorem continuous_fluxes {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hbv : b < v)
    (hs : inSeg a b v ⊆ D) :
    ContinuousOn (fun u => ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 *
      (-S.nu u v) / S.r u v) (Icc a b) ∧
    ContinuousOn (fun u => S.Q u v ^ 2 / S.r u v ^ 2 *
      (-S.nu u v) / S.r u v) (Icc a b) ∧
    ContinuousOn (fun u =>
      ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v)) (Icc a b) := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cx := Calculus.continuousOn_in_section hS.cont_xi hs
  have cq := Calculus.continuousOn_in_section hS.cont_Q hs
  have cm := Calculus.continuousOn_in_section hS.cont_m hs
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
  have hr u (hu : u ∈ Icc a b) := (hS.r_pos _ (hp u hu) (hu.2.trans_lt hbv)).ne'
  have cz := cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun u hu => Complex.ofReal_ne_zero.mpr (hS.nu_neg _ (hp u hu)).ne)
  have cμ : ContinuousOn (fun u => S.mu u v) (Icc a b) :=
    (continuousOn_const.mul cm).div cr hr
  have ce := (cq.pow 2).div (cr.pow 2) (fun u hu => pow_ne_zero _ (hr u hu))
  exact ⟨((cz.norm.pow 2).mul cn.neg).div cr hr,
    (ce.mul cn.neg).div cr hr,
    (((continuousOn_const.sub cμ).mul (cz.norm.pow 2)).add ce).mul cn.neg⟩

/-- [node sec:charged-terminal-interaction#connector-mass-and-flux]
Ratified internal project record: exact incoming balance, mass-ratio control, scalar flux, and
nonnegative electric-loss control, at every partial connector endpoint.
The coefficients depend only on `δ, ρ`; they are uniform in radius, energy,
coupling, scalar amplitude, location and duration. The initial mass budget
is the only energy premise. `dτ = (-ν) du` is explicit in every integral. -/
theorem connector_mass_and_flux {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    {ui e : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    {a b v B E : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ origDomain ui) (hB : 0 < B) (hE : 0 ≤ E)
    (_hstart : S.r a v = B) (hbudget : S.m a v / B ≤ E)
    (hrange : ∀ u ∈ Icc a b, ρ * B ≤ S.r u v)
    (hgap : ∀ u ∈ Icc a b, δ ≤ 1 - S.mu u v) :
    ∀ x ∈ Icc a b,
      (S.m x v + (1 / 2 : ℝ) * (∫ u in a..x,
        ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
          S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v)) = S.m a v) ∧
      (0 ≤ S.m x v ∧ S.m x v / S.r x v ≤ E / ρ) ∧
      (∫ u in a..x, ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 *
        (-S.nu u v) / S.r u v) ≤ 2 * E / (δ * ρ) ∧
      (0 ≤ (∫ u in a..x, S.Q u v ^ 2 / S.r u v ^ 2 *
        (-S.nu u v) / S.r u v) ∧
       (∫ u in a..x, S.Q u v ^ 2 / S.r u v ^ 2 *
        (-S.nu u v) / S.r u v) ≤ 2 * E / ρ) := by
  intro x hx
  have hsx : inSeg a x v ⊆ origDomain ui :=
    fun p hp => hs ⟨hp.1, hp.2.1.trans hx.2, hp.2.2⟩
  have hxm : (x, v) ∈ origDomain ui := hs ⟨hx.1, hx.2, rfl⟩
  have hm0 := (Terminal.mass_monotonicity hS _ hxm).1
  have hmx := Terminal.mass_antitone_in hS hx.1 (hx.2.trans hbv.le) hsx
  have hmB := (div_le_iff₀ hB).1 hbudget
  have hrx := hS.r_pos _ hxm (hx.2.trans_lt hbv)
  have hmass : S.m x v / S.r x v ≤ E / ρ := by
    apply (div_le_iff₀ hrx).2
    have hh := mul_le_mul_of_nonneg_left (hrange x hx) (div_nonneg hE hρ.le)
    have he : E / ρ * (ρ * B) = E * B := by field_simp
    rw [he] at hh
    exact hmx.trans (hmB.trans hh)
  have hbal := connector_mass_balance hS hab hbv hs x hx
  obtain ⟨cz, cq, cf⟩ := continuous_fluxes hS (hx.2.trans_lt hbv) hsx
  let f := fun u => ((1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
    S.Q u v ^ 2 / S.r u v ^ 2) * (-S.nu u v)
  have hfint : (∫ u in a..x, f u) ≤ 2 * E * B := by
    dsimp only [f]
    linarith only [hbal, hm0, hmB]
  have hpoint (u : ℝ) (hu : u ∈ Icc a x) :
      ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 * (-S.nu u v) / S.r u v ≤
        f u / (δ * ρ * B) ∧
      S.Q u v ^ 2 / S.r u v ^ 2 * (-S.nu u v) / S.r u v ≤ f u / (ρ * B) := by
    have hu' : u ∈ Icc a b := ⟨hu.1, hu.2.trans hx.2⟩
    have hp : (u, v) ∈ origDomain ui := hs ⟨hu'.1, hu'.2, rfl⟩
    have hr := hS.r_pos _ hp (hu'.2.trans_lt hbv)
    have hn := (neg_pos.mpr (hS.nu_neg _ hp)).le
    have hz := sq_nonneg ‖S.xi u v / (S.nu u v : ℂ)‖
    have he := div_nonneg (sq_nonneg (S.Q u v)) (sq_nonneg (S.r u v))
    have hg := hδ.le.trans (hgap u hu')
    have hscalar : δ * (‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 * (-S.nu u v)) ≤ f u := by
      dsimp [f]
      nlinarith only [mul_le_mul_of_nonneg_right (hgap u hu') (mul_nonneg hz hn),
        mul_nonneg he hn]
    have helectric : S.Q u v ^ 2 / S.r u v ^ 2 * (-S.nu u v) ≤ f u := by
      dsimp [f]
      nlinarith only [mul_nonneg (mul_nonneg hg hz) hn]
    constructor
    · calc
        _ ≤ (‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 * (-S.nu u v)) / (ρ * B) :=
          div_le_div_of_nonneg_left (mul_nonneg hz hn) (mul_pos hρ hB) (hrange u hu')
        _ ≤ f u / (δ * ρ * B) := by
          apply (div_le_div_iff₀ (mul_pos hρ hB) (mul_pos (mul_pos hδ hρ) hB)).2
          nlinarith only [mul_le_mul_of_nonneg_right hscalar (mul_pos hρ hB).le]
    · exact (div_le_div_of_nonneg_left (mul_nonneg he hn) (mul_pos hρ hB)
        (hrange u hu')).trans (div_le_div_of_nonneg_right helectric (mul_pos hρ hB).le)
  have hzint := intervalIntegral.integral_mono_on hx.1
    (cz.intervalIntegrable_of_Icc (μ := volume) hx.1)
    ((cf.div_const (δ * ρ * B)).intervalIntegrable_of_Icc (μ := volume) hx.1)
    (fun u hu => (hpoint u hu).1)
  have hqint := intervalIntegral.integral_mono_on hx.1
    (cq.intervalIntegrable_of_Icc (μ := volume) hx.1)
    ((cf.div_const (ρ * B)).intervalIntegrable_of_Icc (μ := volume) hx.1)
    (fun u hu => (hpoint u hu).2)
  rw [intervalIntegral.integral_div] at hzint hqint
  have hzbound := hzint.trans (div_le_div_of_nonneg_right hfint (by positivity : 0 ≤ δ * ρ * B))
  have hqbound := hqint.trans (div_le_div_of_nonneg_right hfint (mul_pos hρ hB).le)
  have hzfinal : (2 * E * B) / (δ * ρ * B) = 2 * E / (δ * ρ) := by
    field_simp [hB.ne']
  have hqfinal : (2 * E * B) / (ρ * B) = 2 * E / ρ := by field_simp [hB.ne']
  rw [hzfinal] at hzbound
  rw [hqfinal] at hqbound
  refine ⟨hbal, ⟨hm0, hmass⟩, hzbound, ?_, hqbound⟩
  apply intervalIntegral.integral_nonneg hx.1
  intro u hu
  have hp : (u, v) ∈ origDomain ui := hsx ⟨hu.1, hu.2, rfl⟩
  exact div_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (neg_pos.mpr (hS.nu_neg _ hp)).le) (hS.r_pos _ hp (hu.2.trans_lt (hx.2.trans_lt hbv))).le

end EmcsfAcExtension.Global.Interaction
