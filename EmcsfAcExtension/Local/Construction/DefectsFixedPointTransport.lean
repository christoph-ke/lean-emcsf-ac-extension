module

public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.WaveSystemRecovery
import EmcsfAcExtension.Local.Construction.WaveSystemRadius
import EmcsfAcExtension.Local.Construction.ReconBasic
import EmcsfAcExtension.Local.Construction.DefectsChargeTransport
import EmcsfAcExtension.Local.Construction.DefectsMassTransport
import EmcsfAcExtension.Local.Construction.FullSystemOutgoing

/-! # Field-level defect transports at the C¹ fixed point

The actual geometric and scalar identities discharge every premise of the
charge and mass algebraic cores. This stage is separate from continuity
and zero-axis closure so each proof stays within Lean's default budget.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- Both actual incoming defects satisfy their exact triangular outgoing
transport system at a C¹ Picard fixed point. All geometric and wave inputs
are proved for the reconstruction; neither incoming constraint is assumed.
The fixed positive bounds `l,κ` precede the candidate, and no estimate
constant or second derivative is introduced. -/
theorem defect_transports_of_picard {a b c l κ e : ℝ}
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
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  obtain ⟨cr, cp, _, ct⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨cQ, cm, _, _, cn, _, cG, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  have ct' : ContDiffOn ℝ 1 (Function.uncurry S.theta) D := by
    simpa only [S, Recon.toFields, Function.uncurry] using! ct
  obtain ⟨cx, _, hScalar⟩ := first_order_wave_system hac hcb hl hκ cl ch hlo hgap hL hH
  have hRad := radius_null_identity hac hcb hl hκ cl ch hlo hgap hL
  have hOut := outgoing_equations_of_c1_reconstruction (e := e) hac hcb hl hκ cl ch hlo hgap
  have clu := pdU_lam_on_wedge_of_picard hac hcb cl cG.continuousOn hL
  have hr (p : ℝ × ℝ) (hp : p ∈ D) (huv : p.1 < p.2) : S.r p.1 p.2 ≠ 0 :=
    (Recon.r_pos hl huv
      (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩))
      (fun v hv => hlo (p.1, v) ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩)).ne'
  have hlp (p : ℝ × ℝ) (hp : p ∈ D) : 0 < S.lam p.1 p.2 := hl.trans_le (hlo p hp)
  have hnp (p : ℝ × ℝ) (hp : p ∈ D) : S.nu p.1 p.2 ≠ 0 :=
    (Recon.nu_neg (e := e) (hh := hh)
      (hl.trans_le (hlo (p.1, p.1) ⟨⟨hp.1.1, le_rfl, hp.2.trans hcb⟩, hp.2⟩))).ne
  have hdp (p : ℝ × ℝ) (hp : p ∈ D) : 1 - S.mu p.1 p.2 ≠ 0 :=
    (hκ.trans_le (hgap p hp)).ne'
  have hlu (p : ℝ × ℝ) (hp : p ∈ D) (_ : p.1 < p.2) :
      pdU D S.lam p.1 p.2 = S.rUV p.1 p.2 := by
    change pdU D lam p.1 p.2 = S.rUV p.1 p.2
    rw [clu p hp]
    dsimp only [S, Recon.toFields, Fields.rUV, Fields.mu, Recon.z, Recon.mu]
    ring
  have dZ := defect_transport_charge_of_c1_sources (S := S) (e := e)
    hac hcb cr cQ cp ct' cx hr hdp
    (fun p hp _ => (hRad p hp).2) (fun p hp _ => (hRad p hp).1)
    (fun p hp huv => (hOut p hp huv).2.2.2.1)
    (fun p hp huv => (hScalar p hp huv).1)
    (fun p hp huv => (hOut p hp huv).2.2.2.2.2)
    (fun p hp huv => (hScalar p hp huv).2.1)
    (fun p hp huv => (hScalar p hp huv).2.2)
  have cMV := contDiffOn_reconstructed_mass_source hac hcb hl hκ cl ch hlo hgap
  have dE := defect_transport_mass_of_c1_sources (S := S) (e := e)
    hac hcb cr cl cn cm cQ ct' cx cMV hr
    (fun p hp => (hlp p hp).ne') hnp hdp
    (fun p hp _ => (hRad p hp).2) (fun p hp _ => (hRad p hp).1) hlu
    (fun p hp huv => (hOut p hp huv).2.1)
    (fun p hp huv => (hOut p hp huv).2.2.1)
    (fun p hp huv => (hOut p hp huv).2.2.2.1)
    (fun p hp huv => (hScalar p hp huv).2.1)
    (fun p hp huv => (hScalar p hp huv).2.2)
  exact fun u hu v hv => ⟨dZ u hu v hv, dE u hu v hv⟩

end EmcsfAcExtension.Local.Null
