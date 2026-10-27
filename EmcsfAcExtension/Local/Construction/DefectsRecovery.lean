module

public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.WaveSystemRecovery
import EmcsfAcExtension.Local.Construction.WaveSystemRadius
import EmcsfAcExtension.Local.Construction.ReconBasic
import EmcsfAcExtension.Local.Construction.DefectsFixedPointTransport
import EmcsfAcExtension.Local.Construction.DefectsContinuity
import EmcsfAcExtension.Local.Construction.DefectsProfiles
import EmcsfAcExtension.Local.Construction.Defects
import EmcsfAcExtension.Local.Construction.FullSystemOutgoing

/-! # Actual defect transport and zero-data closure at the C¹ fixed point

The radial profiles and primitive-derived wave equations discharge every
analytic premise of the algebraic defect cores. Zero continuous axis data
then close the incoming Maxwell and mass constraints, internal project record (29)–(30).
-/

public section

open Set Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#defect-transport]
The actual defects are continuous, vanish on the entire axis, satisfy their
triangular outgoing ODE, and recover both incoming constraints on the full
closed construction wedge. Every carrier input is discharged by the preceding
C¹ reconstruction and wave recovery; neither incoming constraint nor a C²
field is assumed. The only bounds are `l > 0` and the S1 gap `κ > 0`, fixed
before the candidate. There are no estimate constants. -/
theorem defect_recovery_of_picard {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    ContinuousOn (Function.uncurry (defectQ e D S)) D ∧
      ContinuousOn (Function.uncurry (defectM D S)) D ∧
      (∀ t ∈ Icc a c, defectQ e D S t t = 0 ∧ defectM D S t t = 0) ∧
      (∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
        HasDerivAt (defectQ e D S u) 0 v ∧
        HasDerivAt (defectM D S u)
          (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * defectM D S u v +
            (S.lam u v * S.Q u v / S.r u v ^ 2) * defectQ e D S u v) v) ∧
      (∀ p ∈ D, pdU D S.Q p.1 p.2 = S.QU e p.1 p.2 ∧ pdU D S.m p.1 p.2 = S.mU p.1 p.2) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  obtain ⟨cr, cp, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨cQ, cm, cμ, _, cn, _, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  obtain ⟨cx, _, _⟩ := first_order_wave_system hac hcb hl hκ cl ch hlo hgap hL hH
  have hnp (p : ℝ × ℝ) (hp : p ∈ D) : S.nu p.1 p.2 ≠ 0 :=
    (Recon.nu_neg (e := e) (hh := hh)
      (hl.trans_le (hlo (p.1, p.1) ⟨⟨hp.1.1, le_rfl, hp.2.trans hcb⟩, hp.2⟩))).ne
  obtain ⟨K, cK, hK, _⟩ := exists_c1_charge_profile (e := e) hac hcb hl cl ch hlo
  have cqR : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) D := by
    apply ((cr.pow 2).mul (cK.pow 2)).congr
    intro p hp
    change Recon.Q e lam hh p.1 p.2 ^ 2 / Recon.r lam p.1 p.2 ^ 2 =
      Recon.r lam p.1 p.2 ^ 2 * K p.1 p.2 ^ 2
    rw [hK p hp]
    by_cases hrp : Recon.r lam p.1 p.2 = 0
    · simp [hrp]
    · field_simp [hrp]
  obtain ⟨cZ, cE⟩ := continuousOn_defects_of_c1_fields (S := S) (e := e)
    hD cr cp cx cQ cm cμ cn cqR hnp
  have ck : ContinuousOn (fun p : ℝ × ℝ =>
      -(‖S.theta p.1 p.2‖ ^ 2 / (S.lam p.1 p.2 * S.r p.1 p.2))) D := by
    apply (contDiffOn_mass_damping hac hcb hl cl ch hlo).continuousOn.neg.congr
    intro p hp
    have hlraw : 0 < lam p.1 p.2 := hl.trans_le (hlo p hp)
    dsimp only [S, Recon.toFields, Function.uncurry, Pi.neg_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlraw]
    by_cases hrp : Recon.r lam p.1 p.2 = 0
    · simp [hrp]
    · field_simp [hrp, hlraw.ne']
  have haxis := defects_axis_values_of_c1_reconstruction (e := e) hac hcb hl cl ch hlo
  have htransport := defect_transports_of_picard hac hcb hl hκ cl ch hlo hgap hL hH
  have cksection (u : ℝ) (hu : u ∈ Icc a c) : ContinuousOn
      (fun v => -(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v))) (Icc u b) := by
    have hs : MapsTo (fun v : ℝ => (u, v)) (Icc u b) D :=
      fun v hv => ⟨⟨hu.1, hv.1, hv.2⟩, hu.2⟩
    exact ck.comp (f := fun v : ℝ => (u, v)) (s := Icc u b)
      ((continuousOn_const (c := u)).prodMk continuousOn_id) hs
  have hclose := incoming_constraints_on_wedge_of_defect_transport
    (a := a) (b := b) (c := c) (e := e) (S := S) cZ cE
    cksection haxis htransport
  exact ⟨cZ, cE, haxis, htransport, hclose⟩


/-- [node restart-sec-independent-null-construction#defect-axis-values]
Both actual defects tend jointly to zero at every closed-wedge axis point.
Continuity and the proved raw zero values include both axis corners; no
incoming constraint is an input. There are no estimate constants. -/
theorem defect_axis_values {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2)
    {t : ℝ} (ht : t ∈ Icc a c) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    Filter.Tendsto (Function.uncurry (defectQ e D S))
        (𝓝[D ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)) (𝓝 0) ∧
      Filter.Tendsto (Function.uncurry (defectM D S))
        (𝓝[D ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)) (𝓝 0) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  obtain ⟨cZ, cE, haxis, _, _⟩ := defect_recovery_of_picard hac hcb hl hκ cl ch hlo hgap hL hH
  have hp : (t, t) ∈ D := ⟨⟨ht.1, le_rfl, ht.2.trans hcb⟩, ht.2⟩
  constructor
  · have h : Filter.Tendsto (Function.uncurry (defectQ e D S))
        (𝓝[D ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)) (𝓝 (defectQ e D S t t)) :=
      (cZ (t, t) hp).mono inter_subset_left
    have hz : defectQ e D S t t = 0 := by
      simpa only [D, S] using! (haxis t ht).1
    rw [hz] at h
    simpa only [D, S] using! h
  · have h : Filter.Tendsto (Function.uncurry (defectM D S))
        (𝓝[D ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)) (𝓝 (defectM D S t t)) :=
      (cE (t, t) hp).mono inter_subset_left
    have hz : defectM D S t t = 0 := by
      simpa only [D, S] using! (haxis t ht).2
    rw [hz] at h
    simpa only [D, S] using! h

/-- [node restart-sec-independent-null-construction#incoming-constraint-closure]
Both incoming constraints hold for the actual C¹ fixed-point reconstruction
on the entire closed wedge. Zero-axis triangular defect transport supplies
them; neither is an input. There are no estimate constants. -/
theorem incoming_constraint_closure {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    ∀ p ∈ D, pdU D S.Q p.1 p.2 = S.QU e p.1 p.2 ∧ pdU D S.m p.1 p.2 = S.mU p.1 p.2 := by
  exact (defect_recovery_of_picard hac hcb hl hκ cl ch hlo hgap hL hH).2.2.2.2

/-- [node restart-sec-independent-null-construction#defect-transport]
The outgoing derivatives of the actual incoming defects satisfy the exact
triangular system with no extra Hawking-gap factor in the mass coefficient.
The geometric and wave identities are discharged by C¹ fixed-point recovery.
There are no estimate constants or higher regularity hypotheses. -/
theorem defect_transport {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (defectQ e D S u) 0 v ∧
      HasDerivAt (defectM D S u)
        (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * defectM D S u v +
          (S.lam u v * S.Q u v / S.r u v ^ 2) * defectQ e D S u v) v := by
  exact (defect_recovery_of_picard hac hcb hl hκ cl ch hlo hgap hL hH).2.2.2.1

end EmcsfAcExtension.Local.Null
