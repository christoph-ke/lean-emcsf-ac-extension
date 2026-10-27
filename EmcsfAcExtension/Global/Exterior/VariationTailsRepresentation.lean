module

public import EmcsfAcExtension.Global.Exterior.DerivativeSource
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The exact expansion-ratio density representation

The continuous multiplier is identified literally with the expansion
ratio and unitary electromagnetic phase of `charged_SF_new_version.tex:L1410–L1412`.
The sole rough factor is the fixed initial L¹ outgoing derivative. This
is the precise multiplier form in approved internal project record (R1).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#derivative-ac-representation]
The fixed-density representation with the literal expansion-ratio/phase
multiplier and a jointly continuous remainder. The common label-null set
precedes every row. No bound or continuity of the initial derivative is
assumed, and no implicit constants occur. -/
theorem derivative_ac_representation_exact_multiplier
    {ui e a b c d : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    (∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      HasDerivAt (S.a u) (densityRepresentative e S a u v) v) ∧
    ContinuousOn (fun p : ℝ × ℝ => (S.lam a p.2 / S.lam p.1 p.2 : ℝ) *
      Complex.exp (-I * e * ∫ s in a..p.1, S.A s p.2)) (Icc a b ×ˢ Icc c d) ∧
    ∃ R : ℝ → ℝ → ℂ, ContinuousOn R.uncurry (Icc a b ×ˢ Icc c d) ∧
      ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        densityRepresentative e S a u v =
          (S.lam a v / S.lam u v : ℝ) *
            Complex.exp (-I * e * ∫ s in a..u, S.A s v) * deriv (S.a a) v + R u v := by
  let C₀ : ℝ → ℝ → ℂ := fun u v =>
    ((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) : ℂ) - I * e * S.A u v
  obtain ⟨C, hC, hCe⟩ := Calculus.exists_continuous_rectangle_extension (f := C₀)
    hab.le hcd.le (Calculus.continuousOn_density_coefficient hS hrect)
  obtain ⟨F, hF, hFe⟩ := Calculus.exists_continuous_rectangle_extension
    hab.le hcd.le (Calculus.continuousOn_rawDensitySource hS hrect)
  have hcanonical := Calculus.densityRepresentative_eq_transportDensity_of_coefficients
    hS hab hcd hrect hC (fun p hp => hCe hp) hFe
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  have hE (u : ℝ) (hu : u ∈ Icc a b) (v : ℝ) (hv : v ∈ Icc c d) :
      Complex.exp (∫ s in a..u, C s v) =
        (S.lam a v / S.lam u v : ℝ) * Complex.exp (-I * e * ∫ s in a..u, S.A s v) := by
    have hs : inSeg a u v ⊆ origDomain ui := by
      rintro ⟨x, y⟩ ⟨hx₁, hx₂, rfl⟩
      exact (hrect ⟨⟨hx₁, hx₂.trans hu.2⟩, hv⟩).1
    have hsec := Local.IsSolution.in_section hS hu.1
      (hu.2.trans_lt (hbc.trans_le hv.1)) hs
    apply Calculus.exp_integral_eq_ratio_phase_of_transport e hu.1 hsec.2.1.1
      (fun x hx => (hS.lam_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩)).ne')
      ((hC.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a u)
      ((Calculus.continuousOn_in_section hS.cont_A hs).intervalIntegrable_of_Icc hu.1)
    · filter_upwards [hsec.2.1.2, ae_restrict_mem measurableSet_Icc] with x hx hxm
      apply hx.ofReal_comp.congr_deriv
      change (S.rUV x v : ℂ) = -(C x v + I * e * S.A x v) * S.lam x v
      have heC : C x v = C₀ x v := hCe
        (show (x, v) ∈ Icc a b ×ˢ Icc c d from ⟨⟨hxm.1, hxm.2.trans hu.2⟩, hv⟩)
      rw [heC]
      have halg := congrArg (fun z : ℝ => (z : ℂ)) (Calculus.density_coefficient_mul_lam S x v)
      dsimp only [C₀]
      push_cast at halg ⊢
      linear_combination halg
    · exact ⟨hu.1, le_rfl⟩
  obtain ⟨P, R, hP, hR, hPR⟩ := Density.exists_continuous_transport_factors hC hF a
  have hR₀ (u v : ℝ) : Density.transportDensity C F (fun _ => 0) a u v = R u v := by
    simpa only [Density.fixedDensity, mul_zero, zero_add] using hPR (fun _ => 0) u v
  refine ⟨?_, ?_, R, hR.continuousOn, ?_⟩
  · obtain ⟨P₀, Rc, hP₀, hRc, hrep, hprim⟩ := Calculus.exists_density_factors hS hab hcd hrect
    have hinit := (hS.ac_out a c d hcd.le (by
      rintro ⟨u, v⟩ ⟨rfl, hv⟩
      exact (hrect ⟨⟨le_rfl, hab.le⟩, hv⟩).1)).2.2.2.2
    filter_upwards [Density.ae_forall_hasDerivAt_of_fixedDensity_representation hcd.le
      hP₀ hRc hinit.intervalIntegrable_deriv_complex hprim,
      ae_restrict_mem measurableSet_Icc] with v hv hvm u hu
    rw [hrep u hu v hvm]
    exact hv u hu
  · have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Complex.exp (∫ s in a..p.1, C s p.2)) (Icc a b ×ˢ Icc c d) :=
      (Complex.continuous_exp.comp (Density.continuous_incoming_primitive hC a)).continuousOn
    apply hcont.congr
    intro p hp
    exact (hE p.1 hp.1 p.2 hp.2).symm
  · intro u hu v hv
    calc
      densityRepresentative e S a u v = Density.transportDensity C F (deriv (S.a a)) a u v :=
        hcanonical u hu v hv
      _ = Complex.exp (∫ s in a..u, C s v) * deriv (S.a a) v +
          Density.transportDensity C F (fun _ => 0) a u v := by
        simp only [Density.transportDensity, zero_add, mul_add]
      _ = _ := by rw [hE u hu v hv, hR₀]

/-- [internal] The literal source integral in the expansion-ratio
representation is jointly continuous on every proper rectangle. Its
continuity does not depend on regularity of the initial derivative. -/
theorem density_source_remainder_continuousOn
    {ui e a b c d : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ s in a..p.1,
      (S.lam s p.2 / S.lam p.1 p.2 : ℝ) *
        Complex.exp (-I * e * ∫ t in s..p.1, S.A t p.2) * rawDensitySource e S s p.2)
      (Icc a b ×ˢ Icc c d) := by
  obtain ⟨_, _, R, hR, hrep⟩ := derivative_ac_representation_exact_multiplier hS hab hcd hrect
  apply hR.congr
  intro p hp
  have he := hrep p.1 hp.1 p.2 hp.2
  rw [densityRepresentative_def] at he
  exact add_left_cancel he

end EmcsfAcExtension.Global.Exterior
