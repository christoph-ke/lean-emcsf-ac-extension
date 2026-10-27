module

public import EmcsfAcExtension.Local.Construction.FullSystemCharge
public import EmcsfAcExtension.Local.Construction.FullSystemDamping
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # A nonsingular joint C¹ normalized mass profile

The literal integrating factor is retained. One radial power is removed
from the forcing before the rescaled integration removes the second.
This is the mass formula of internal project record (6), written using its primitive.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- Factor a terminal integrating factor on a closed outgoing interval.
The only analytic premise is integrability of its actual damping. -/
theorem factor_integral_of_integrable {a f : ℝ → ℝ} {u v : ℝ} (_huv : u ≤ v)
    (ha : IntervalIntegrable a volume u v) :
    (∫ s in u..v, f s * Real.exp (-∫ t in s..v, a t)) =
      Real.exp (-∫ t in u..v, a t) *
        ∫ s in u..v, Real.exp (∫ t in u..s, a t) * f s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  have hs' : s ∈ uIcc u v := hs
  have hsub := intervalIntegral.integral_interval_sub_left ha
    (ha.mono_set (uIcc_subset_uIcc left_mem_uIcc hs'))
  rw [show -(∫ t in s..v, a t) = -(∫ t in u..v, a t) + ∫ t in u..s, a t by
    linarith [hsub], Real.exp_add]
  ring

/-- A source with one exact radial-width factor gains a second factor by
radial integration. The formula includes the collapsed interval. -/
theorem integral_width_mul_eq_moment (F : ℝ → ℝ → ℝ) (u v : ℝ) :
    (∫ s in u..v, (s - u) * F u s) =
      (v - u) ^ 2 * ∫ t in (0 : ℝ)..1, t * F u (u + (v - u) * t) := by
  rw [integral_eq_width_smul_radial_average (fun u v => (v - u) * F u v) u v]
  simp only [smul_eq_mul]
  have he : (∫ t in (0 : ℝ)..1,
      (u + (v - u) * t - u) * F u (u + (v - u) * t)) =
      (v - u) * ∫ t in (0 : ℝ)..1, t * F u (u + (v - u) * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [he]
  ring

/-- The literal reconstructed mass has a joint C¹ profile `V = 2m/r²`,
vanishing on the axis. The charge profile is an independently constructed
radial intermediate; neither incoming constraint is assumed. The positive
lower bound `l` precedes the candidate and there are no new constants. -/
theorem exists_c1_mass_profile {a b c l e : ℝ} (hac : a < c) (hcb : c ≤ b)
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} (hl : 0 < l)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2) :
    ∃ V : ℝ → ℝ → ℝ,
      ContDiffOn ℝ 1 (Function.uncurry V) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        Recon.m e lam hh p.1 p.2 = Recon.r lam p.1 p.2 ^ 2 * V p.1 p.2 / 2) ∧
      (∀ t ∈ Icc a c, V t t = 0) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let L (u v : ℝ) := ∫ t in (0 : ℝ)..1, lam u (u + (v - u) * t)
  let T (u v : ℝ) := ‖Recon.ratio lam hh u v‖ ^ 2 / (v - u)
  let A (u v : ℝ) := lam u v * ‖Recon.ratio lam hh u v‖ ^ 2 / Recon.r lam u v
  let J (u v : ℝ) := ∫ s in u..v, A u s
  obtain ⟨K, cK, hK, hK0⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  let H (u v : ℝ) := lam u v * (T u v + (v - u) * L u v ^ 2 * K u v ^ 2)
  let F (u v : ℝ) := Real.exp (J u v) * H u v
  let V (u v : ℝ) := Real.exp (-J u v) / L u v ^ 2 *
    ∫ t in (0 : ℝ)..1, t * F u (u + (v - u) * t)
  have cL : ContDiffOn ℝ 1 (Function.uncurry L) D := contDiffOn_radial_average hac hcb cl
  have hL (p : ℝ × ℝ) (hp : p ∈ D) : L p.1 p.2 ≠ 0 :=
    (hl.trans_le (radial_average_lam_lower cl.continuousOn hlo hp)).ne'
  have hr (u v : ℝ) : Recon.r lam u v = (v - u) * L u v :=
    integral_eq_width_smul_radial_average lam u v
  obtain ⟨_, _, cf, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  have cT : ContDiffOn ℝ 1 (Function.uncurry T) D :=
    contDiffOn_norm_sq_div_width hac hcb cf (fun t _ => Recon.ratio_axis)
  have cA : ContDiffOn ℝ 1 (Function.uncurry A) D := contDiffOn_mass_damping hac hcb hl cl ch hlo
  have cJ : ContDiffOn ℝ 1 (Function.uncurry J) D := contDiffOn_radial_primitive hac hcb cA
  have cH : ContDiffOn ℝ 1 (Function.uncurry H) D :=
    cl.mul (cT.add (((contDiffOn_snd.sub contDiffOn_fst).mul (cL.pow 2)).mul (cK.pow 2)))
  have cF : ContDiffOn ℝ 1 (Function.uncurry F) D :=
    (Real.contDiff_exp.comp_contDiffOn cJ).mul cH
  have cV : ContDiffOn ℝ 1 (Function.uncurry V) D :=
    ((Real.contDiff_exp.comp_contDiffOn cJ.neg).div (cL.pow 2)
      (fun p hp => pow_ne_zero 2 (hL p hp))).mul
      (by simpa only [smul_eq_mul, pow_one] using! contDiffOn_radial_moment hac hcb 1 cF)
  have hforce (p : ℝ × ℝ) (hp : p ∈ D) :
      lam p.1 p.2 * (‖Recon.ratio lam hh p.1 p.2‖ ^ 2 +
        Recon.Q e lam hh p.1 p.2 ^ 2 / Recon.r lam p.1 p.2 ^ 2) =
        (p.2 - p.1) * H p.1 p.2 := by
    rw [hK p hp, hr]
    dsimp [H, T]
    rcases hp.1.2.1.eq_or_lt with he | he
    · simp [he]
    · have hx := (sub_pos.mpr he).ne'
      field_simp [hx, hL p hp]
  refine ⟨V, cV, ?_, ?_⟩
  · intro p hp
    have hs : MapsTo (fun s => (p.1, s)) (Icc p.1 p.2) D :=
      fun s hs => ⟨⟨hp.1.1, hs.1, hs.2.trans hp.1.2.2⟩, hp.2⟩
    have ia : IntervalIntegrable (A p.1) volume p.1 p.2 := by
      have hc : ContinuousOn (A p.1) (Icc p.1 p.2) :=
        cA.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hs
      exact hc.intervalIntegrable_of_Icc hp.1.2.1
    have hfact := factor_integral_of_integrable hp.1.2.1 (f := fun s =>
      lam p.1 s * (‖Recon.ratio lam hh p.1 s‖ ^ 2 +
        Recon.Q e lam hh p.1 s ^ 2 / Recon.r lam p.1 s ^ 2)) ia
    have he : (∫ s in p.1..p.2, Real.exp (J p.1 s) *
        (lam p.1 s * (‖Recon.ratio lam hh p.1 s‖ ^ 2 +
          Recon.Q e lam hh p.1 s ^ 2 / Recon.r lam p.1 s ^ 2))) =
        (p.2 - p.1) ^ 2 * ∫ t in (0 : ℝ)..1,
          t * F p.1 (p.1 + (p.2 - p.1) * t) := by
      rw [← integral_width_mul_eq_moment F]
      apply intervalIntegral.integral_congr
      intro s hs'
      dsimp only
      have hs'' : s ∈ Icc p.1 p.2 := by simpa only [uIcc_of_le hp.1.2.1] using hs'
      rw [hforce (p.1, s) (hs hs'')]
      dsimp [F]
      ring
    change Recon.m e lam hh p.1 p.2 = Recon.r lam p.1 p.2 ^ 2 *
      (Real.exp (-J p.1 p.2) / L p.1 p.2 ^ 2 *
        ∫ t in (0 : ℝ)..1, t * F p.1 (p.1 + (p.2 - p.1) * t)) / 2
    rw [Recon.m, hfact, he, hr]
    field_simp [hL p hp]
    ring
  · intro t _
    simp [V, F, H, T, J]

end EmcsfAcExtension.Local.Null
