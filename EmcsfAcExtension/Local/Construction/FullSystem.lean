module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.DefectsRecovery
import EmcsfAcExtension.Local.Construction.WaveSystemRecovery
import EmcsfAcExtension.Local.Construction.WaveSystemRadius
import EmcsfAcExtension.Local.Construction.FullSystemOutgoing
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Recovery of the full reduced system in the C¹ class

The internal project record construction interface: all nine primary fields are jointly C¹
on the original closed wedge and satisfy the thirteen reduced equations.
The two literal Picard fixed-point equations remain explicit inputs.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Null

/--
C¹ form of the regularity node under internal project record: the fixed-point pair and all
nine reconstructed primary fields are jointly C¹ on the original closed
wedge. The incoming scalar jet uses its linear primitive. Neither incoming
constraint nor any C² hypothesis is an input. Bounds `l,κ` precede the
candidate and there are no estimate constants. -/
theorem smooth_regularity_of_picard {a b c l κ e : ℝ}
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
    ContDiffOn ℝ 1 (Function.uncurry hh) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.r) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.lam) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.nu) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.m) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.Q) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.phi) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.A) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.theta) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.xi) D := by
  obtain ⟨cr, cp, _, ct⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨cQ, cm, _, _, cn, cA, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  obtain ⟨cx, _, _⟩ := first_order_wave_system hac hcb hl hκ cl ch hlo hgap hL hH
  refine ⟨ch, cr, cl, cn, cm, cQ, cp, cA, ?_, cx⟩
  simpa only [Recon.toFields, Function.uncurry] using! ct

/--
C¹ form of full-system recovery under internal project record. The actual reconstructed fields
satisfy `IsC1Solution` on the closed construction wedge and retain the zero
axis gauge. The incoming charge and mass equations are proved by the actual
defect transports. Both Picard equations and the nondegenerate S1 bounds
remain explicit. No conclusion bundle or higher regularity is assumed. -/
theorem smooth_full_system_of_picard {a b c l κ e : ℝ}
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
    IsC1Solution e (Recon.toFields e lam hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ∀ t ∈ Icc a c, (Recon.toFields e lam hh).A t t = 0 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  obtain ⟨_, cr, _, cn, cm, cQ, cp, cA, ct, cx⟩ :=
    smooth_regularity_of_picard hac hcb hl hκ cl ch hlo hgap hL hH
  have hRad := radius_null_identity hac hcb hl hκ cl ch hlo hgap hL
  have hOut := outgoing_equations_of_c1_reconstruction (e := e) hac hcb hl hκ cl ch hlo hgap
  obtain ⟨_, _, hScalar⟩ := first_order_wave_system hac hcb hl hκ cl ch hlo hgap hL hH
  obtain ⟨_, _, _, _, hIn⟩ := defect_recovery_of_picard hac hcb hl hκ cl ch hlo hgap hL hH
  obtain ⟨_, _, _, _, _, _, cG, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  have clu := pdU_lam_on_wedge_of_picard hac hcb cl cG.continuousOn hL
  refine ⟨{ subset := fun p hp => hp.1.2.1
            r_pos := ?_
            lam_pos := fun p hp => hl.trans_le (hlo p hp)
            nu_neg := ?_
            one_sub_mu_pos := fun p hp => hκ.trans_le (hgap p hp)
            c1_r := cr
            c1_lam := cl
            c1_nu := cn
            c1_m := cm
            c1_Q := cQ
            c1_phi := cp
            c1_A := cA
            c1_theta := ct
            c1_xi := cx
            eq_v := ?_
            eq_u := ?_
            axis := ?_ }, fun _ _ => Recon.A_axis⟩
  · intro p hp huv
    exact Recon.r_pos hl huv
      (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩))
      (fun v hv => hlo (p.1, v) ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩)
  · intro p hp
    exact Recon.nu_neg (hl.trans_le (hlo (p.1, p.1)
      ⟨⟨hp.1.1, le_rfl, hp.2.trans hcb⟩, hp.2⟩))
  · intro p hp huv
    obtain ⟨rv, nv, mv, qv, av, pv⟩ := hOut p hp huv
    exact ⟨rv, nv, mv, qv, av, pv, (hScalar p hp huv).2.2⟩
  · intro p hp huv
    have hlu : pdU D S.lam p.1 p.2 = S.rUV p.1 p.2 := by
      change pdU D lam p.1 p.2 = S.rUV p.1 p.2
      rw [clu p hp]
      dsimp only [S, Recon.toFields, Fields.rUV, Fields.mu, Recon.z, Recon.mu]
      ring
    exact ⟨(hRad p hp).2, hlu, (hIn p hp).2, (hIn p hp).1,
      (hScalar p hp huv).1, (hScalar p hp huv).2.1⟩
  · intro t _
    obtain ⟨hr, hm, hq, _, hln, ha, hb⟩ :=
      Recon.toFields_axis (e := e) (lam := lam) (hh := hh) (u := t)
    exact ⟨hr, hm, hq, hln, ha, hb⟩

end EmcsfAcExtension.Local.Null
