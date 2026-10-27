module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.WaveSystemC1
import EmcsfAcExtension.Local.Construction.WaveSystemFixedPoint
import EmcsfAcExtension.Local.Construction.WaveSystemRadius
import EmcsfAcExtension.Local.Construction.FullSystemOutgoing
import EmcsfAcExtension.Local.Construction.FullSystemIncomingRegularity
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Recovery and C¹ regularity of the actual incoming scalar field

internal project record (24)–(28). The outgoing primitive defining `toFields.xi`
is identified with `r D_u φ`. Its missing incoming first regularity comes
from the normalized incoming scalar's linear primitive on the same wedge.
-/

public section

open Set Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#first-order-wave-system]
The actual reconstructed ξ is jointly C¹ and equals `r D_u φ`; both frozen
first-order wave transports hold off axis, including the upper outgoing
edge. Both Picard equations are explicit. The only bounds are the fixed
positive λ lower bound and S1 Hawking gap. No C² field or incoming charge
or mass constraint is assumed, and no estimate constant is introduced. -/
theorem first_order_wave_system {a b c l κ e : ℝ}
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
    ContDiffOn ℝ 1 (Function.uncurry S.xi) D ∧
      (∀ p ∈ D, S.xi p.1 p.2 = (S.r p.1 p.2 : ℂ) *
        (pdU D S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2)) ∧
      (∀ p ∈ D, p.1 < p.2 →
        pdU D S.phi p.1 p.2 = S.phiU e p.1 p.2 ∧
        pdU D S.theta p.1 p.2 = S.thetaU e p.1 p.2 ∧
        pdV D S.xi p.1 p.2 = S.xiV e p.1 p.2) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let S := Recon.toFields e lam hh
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  obtain ⟨cr, cp, _, ct⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨_, _, cμ, _, cn, cA, cG, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  have ct' : ContDiffOn ℝ 1 (Function.uncurry S.theta) D := by
    simpa only [S, Recon.toFields, Function.uncurry] using! ct
  have hRad := radius_null_identity hac hcb hl hκ cl ch hlo hgap hL
  have hOut := outgoing_equations_of_c1_reconstruction (e := e) hac hcb hl hκ cl ch hlo hgap
  obtain ⟨hNv, hWraw⟩ := rphi_wave_identity hac hcb hl hκ cl ch hlo hgap hL hH
  have hJval (p : ℝ × ℝ) : (S.lam p.1 p.2 : ℂ) * S.phi p.1 p.2 + S.theta p.1 p.2 =
      (lam p.1 p.2 : ℂ) * hh p.1 p.2 := by
    dsimp only [S, Recon.toFields, Recon.ratio]
    ring
  have hWfield (p : ℝ × ℝ) (hp : p ∈ D) (huv : p.1 < p.2) :
      pdU D (fun u v => (S.lam u v : ℂ) * S.phi u v + S.theta u v) p.1 p.2 =
      (S.nu p.1 p.2 : ℂ) * S.lam p.1 p.2 /
          ((1 - (S.mu p.1 p.2 : ℂ)) * (S.r p.1 p.2 : ℂ) ^ 2) *
        ((S.mu p.1 p.2 : ℂ) - (S.Q p.1 p.2 : ℂ) ^ 2 / (S.r p.1 p.2 : ℂ) ^ 2 -
          I * e * S.Q p.1 p.2) * ((S.r p.1 p.2 : ℂ) * S.phi p.1 p.2) -
        I * e * S.A p.1 p.2 * ((S.lam p.1 p.2 : ℂ) * S.phi p.1 p.2 + S.theta p.1 p.2) := by
    have heq : EqOn
        (Function.uncurry (fun u v => (S.lam u v : ℂ) * S.phi u v + S.theta u v))
        (Function.uncurry (fun u v => (lam u v : ℂ) * hh u v)) D := by
      intro q _
      simpa only [Function.uncurry_def] using! hJval q
    rw [pdU_congr heq hp, hJval p]
    simpa only [S, Recon.toFields, Fields.mu, Recon.mu] using! hWraw p hp huv
  have hr (p : ℝ × ℝ) (hp : p ∈ D) (huv : p.1 < p.2) : S.r p.1 p.2 ≠ 0 :=
    (Recon.r_pos hl huv
      (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩))
      (fun v hv => hlo (p.1, v) ⟨⟨hp.1.1, hv.1, hv.2.trans hp.1.2.2⟩, hp.2⟩)).ne'
  have hn (p : ℝ × ℝ) (hp : p ∈ D) : S.nu p.1 p.2 ≠ 0 :=
    (Recon.nu_neg (e := e) (hh := hh)
      (hl.trans_le (hlo (p.1, p.1) ⟨⟨hp.1.1, le_rfl, hp.2.trans hcb⟩, hp.2⟩))).ne
  have clu := pdU_lam_on_wedge_of_picard hac hcb cl cG.continuousOn hL
  obtain ⟨X, cX, hX0, hXp, htu, dX⟩ := first_order_wave_system_of_c1_primitives (S := S)
    (e := e) hac hcb cr cl cn cp cA ct' hr
    (fun p hp => (hκ.trans_le (hgap p hp)).ne')
    (fun _ _ => Recon.r_axis) (fun p hp => (hRad p hp).2)
    (fun p hp _ => by
      change pdU D lam p.1 p.2 = S.rUV p.1 p.2
      rw [clu p hp]
      dsimp only [S, Recon.toFields, Fields.rUV, Fields.mu, Recon.z, Recon.mu]
      ring)
    (fun p hp huv => (hOut p hp huv).2.1)
    (fun p hp huv => (hOut p hp huv).2.2.2.2.2)
    (fun p hp huv => (hOut p hp huv).2.2.2.2.1)
    (fun p hp => (hNv p hp).trans (hJval p).symm) hWfield
  let B (u v : ℝ) := lam u v / Recon.r lam u v * Recon.z e lam hh u v
  let J (u v : ℝ) := I * e * lam u v * Recon.Q e lam hh u v * Recon.phi lam hh u v /
    ((1 - (Recon.mu e lam hh u v : ℂ)) * Recon.r lam u v)
  let G (u v : ℝ) := -((S.nu u v : ℂ) * pdV D S.phi u v) + (S.nu u v : ℂ) * J u v
  obtain ⟨cBraw, cJraw⟩ := contDiffOn_wave_coefficients hac hcb hl hκ cl ch hlo hgap
  have cB : ContDiffOn ℝ 1 (Function.uncurry B) D := by
    simpa only [Function.uncurry] using! cBraw
  have cJ : ContDiffOn ℝ 1 (Function.uncurry J) D := by
    simpa only [Function.uncurry] using! cJraw
  have cGG : ContinuousOn (Function.uncurry G) D :=
    ((Complex.continuous_ofReal.comp_continuousOn cn.continuousOn).mul
      (continuousOn_pdV cp hD)).neg.add
      ((Complex.continuous_ofReal.comp_continuousOn cn.continuousOn).mul cJ.continuousOn)
  have hG (p : ℝ × ℝ) (hp : p ∈ D) (huv : p.1 < p.2) : G p.1 p.2 = S.xiV e p.1 p.2 := by
    dsimp only [G]
    rw [(hOut p hp huv).2.2.2.2.2]
    dsimp only [Fields.xiV, Fields.waveSource, Fields.phiV, J, S, Recon.toFields,
      Fields.mu, Recon.mu]
    ring
  have dXG (u : ℝ) (hu : u ∈ Icc a c) (v : ℝ) (hv : v ∈ Ioo u b) :
      HasDerivAt (X u) (G u v) v := by
    convert dX u hu v hv using 1
    rw [hG (u, v) ⟨⟨hu.1, hv.1.le, hv.2.le⟩, hu.2⟩ hv.1]
    dsimp only [Fields.xiV, Fields.waveSource]
  have hXG := eq_radial_primitive_of_off_axis_derivative cX cGG hX0 dXG (fun _ _ _ => rfl)
  have hXi := eq_radial_primitive_of_off_axis_derivative cX cGG hX0 dXG hG
  have hXi' (p : ℝ × ℝ) (hp : p ∈ D) : X p.1 p.2 = S.xi p.1 p.2 := by
    rw [hXi p hp]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [Fields.xiV, Fields.waveSource, S, Recon.toFields, Fields.mu, Recon.mu]
  have cg : ContDiffOn ℝ 1 (fun u => hh u u) (Icc a c) :=
    ch.comp (contDiffOn_id.prodMk contDiffOn_id)
      (fun u hu => ⟨⟨hu.1, le_rfl, hu.2.trans hcb⟩, hu.2⟩)
  have dnu (u : ℝ) (hu : u ∈ Icc a c) (v : ℝ) (hv : v ∈ Ioo u b) :
      HasDerivAt (S.nu u) (S.nu u v * B u v) v := by
    have hp : (u, v) ∈ D := ⟨⟨hu.1, hv.1.le, hv.2.le⟩, hu.2⟩
    have hd := (hasDerivWithinAt_pdV cn hp (s := Icc u b)
      (fun s hs => ⟨⟨hu.1, hs.1, hs.2⟩, hu.2⟩)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    have hnv : pdV D (Recon.nu e lam hh) u v = S.rUV u v := by
      simpa only [S, Recon.toFields] using! (hOut (u, v) hp hv.1).2.1
    rw [hnv] at hd
    have hcoeff : S.nu u v * B u v = S.rUV u v := by
      dsimp only [B, S, Recon.toFields, Fields.rUV, Fields.mu, Recon.mu, Recon.z]
      ring
    rw [hcoeff]
    simpa only [S, Recon.toFields] using! hd
  have cX1 := contDiffOn_incoming_wave_jet_of_linear_primitive hac hcb cp cn cB cJ cX cg hn
    (fun _ _ => Recon.phi_axis) hX0 dnu dXG
  have cXi : ContDiffOn ℝ 1 (Function.uncurry S.xi) D :=
    cX1.congr (fun p hp => (hXi' p hp).symm)
  refine ⟨cXi, (fun p hp => (hXi' p hp).symm.trans (hXp p hp)), ?_⟩
  intro p hp huv
  have hrC : (S.r p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast hr p hp huv
  have hpu : pdU D S.phi p.1 p.2 = S.phiU e p.1 p.2 := by
    have h := (hXi' p hp).symm.trans (hXp p hp)
    dsimp only [Fields.phiU]
    rw [h]
    field_simp [hrC]
    ring
  have htheta : pdU D S.theta p.1 p.2 = S.thetaU e p.1 p.2 := by
    rw [htu p hp huv, hXi' p hp]
    dsimp only [Fields.thetaU, Fields.waveSource]
  have hxi : pdV D S.xi p.1 p.2 = S.xiV e p.1 p.2 := by
    have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b) D :=
      fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
    have hd := Recon.hasDerivWithinAt_primitive
      (cGG.comp (continuousOn_const.prodMk continuousOn_id) hs) ⟨hp.1.2.1, hp.1.2.2⟩
    have heq (v : ℝ) (hv : v ∈ Icc p.1 b) : S.xi p.1 v = ∫ s in p.1..v, G p.1 s :=
      (hXi' (p.1, v) (hs hv)).symm.trans (hXG (p.1, v) (hs hv))
    have hd' := hd.congr heq (heq p.2 ⟨hp.1.2.1, hp.1.2.2⟩)
    have huD := uniqueDiffOn_Icc (huv.trans_le hp.1.2.2) p.2 ⟨hp.1.2.1, hp.1.2.2⟩
    exact ((hasDerivWithinAt_pdV cXi hp hs).derivWithin huD).symm.trans
      ((hd'.derivWithin huD).trans (hG p hp huv))
  exact ⟨hpu, htheta, hxi⟩

end EmcsfAcExtension.Local.Null
