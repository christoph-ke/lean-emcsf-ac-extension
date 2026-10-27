module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
import EmcsfAcExtension.Local.Construction.FullSystemRegularity
import EmcsfAcExtension.Local.Construction.CenterOrders

/-! # The outgoing equations as actual domain partials

The landed internal project record sectional equations are identified with the domain
partials after the C¹ upgrade. Compact first-jet bounds are obtained inside
the proof and are not extra assumptions on the cone datum.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- The six already reconstructed outgoing equations hold as actual domain
partials off axis on the entire closed wedge. Only the reconstructed pair's
C¹ regularity, positive λ lower bound, and S1 gap are inputs. Compact bounds
used to invoke internal project record are internal witnesses, not estimate constants or
smallness hypotheses. The ξ equation is recovered separately from the wave
primitive. -/
theorem outgoing_equations_of_c1_reconstruction {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    ∀ p ∈ D, p.1 < p.2 →
      pdV D S.r p.1 p.2 = S.lam p.1 p.2 ∧
      pdV D S.nu p.1 p.2 = S.rUV p.1 p.2 ∧
      pdV D S.m p.1 p.2 = S.mV p.1 p.2 ∧
      pdV D S.Q p.1 p.2 = S.QV e p.1 p.2 ∧
      pdV D S.A p.1 p.2 = S.AV p.1 p.2 ∧
      pdV D S.phi p.1 p.2 = S.phiV p.1 p.2 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  dsimp only
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  obtain ⟨CU, hbU⟩ := (isCompact_wedge a b c).exists_bound_of_continuousOn cl.continuousOn
  obtain ⟨CH, hbH⟩ := (isCompact_wedge a b c).exists_bound_of_continuousOn ch.continuousOn
  obtain ⟨CD, hbD⟩ := (isCompact_wedge a b c).exists_bound_of_continuousOn (continuousOn_pdV ch hD)
  obtain ⟨cr, cp, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨cQ, cm, _, _, cn, cA, _, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  intro p hp huv
  have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b) D :=
    fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
  have hlen : b - p.1 ≤ b - a := by linarith only [hp.1.1]
  have hOC := outgoing_constraints (e := e) (lam := lam) (hh := hh)
    (h' := pdV D hh p.1) hl (le_max_left l (max 0 CU))
    (le_max_left 0 CH) (le_max_left 0 CD) (sub_nonneg.mpr (hac.le.trans hcb)) hκ
    (hp.1.2.1.trans hp.1.2.2) hlen
    (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hs)
    (fun v hv => ⟨hlo (p.1, v) (hs hv),
      (le_abs_self _).trans ((show |lam p.1 v| ≤ CU from by
        simpa only [Real.norm_eq_abs, Function.uncurry_def] using! hbU (p.1, v) (hs hv)).trans
        ((le_max_right 0 CU).trans (le_max_right l (max 0 CU))))⟩)
    (fun v hv => hasDerivWithinAt_pdV ch (hs hv) hs)
    (fun v hv => ⟨(hbH (p.1, v) (hs hv)).trans (le_max_right 0 CH),
      (hbD (p.1, v) (hs hv)).trans (le_max_right 0 CD)⟩)
    (fun v hv => hgap (p.1, v) (hs hv))
  obtain ⟨dr, _, dn, dm, dq, da, dp, _, _⟩ := hOC.1 p.2 ⟨hp.1.2.1, hp.1.2.2⟩
  have huniq := uniqueDiffOn_Icc (huv.trans_le hp.1.2.2) p.2 ⟨hp.1.2.1, hp.1.2.2⟩
  have resolve {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → ℝ → E} {k : E} (cf : ContDiffOn ℝ 1 (Function.uncurry f) D)
      (df : HasDerivWithinAt (f p.1) k (Icc p.1 b) p.2) : pdV D f p.1 p.2 = k :=
    ((hasDerivWithinAt_pdV cf hp hs).derivWithin huniq).symm.trans (df.derivWithin huniq)
  exact ⟨resolve cr dr, resolve cn dn, resolve cm dm, resolve cQ dq,
    resolve cA da, resolve cp (dp huv)⟩

end EmcsfAcExtension.Local.Null
