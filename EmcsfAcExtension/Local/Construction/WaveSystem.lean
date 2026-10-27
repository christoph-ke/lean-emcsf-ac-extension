module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Local.Algebra.Defects
import EmcsfAcExtension.Local.Construction.WaveSystemPicard
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Differential wave product recovered from the incoming transports

The product-rule step at `charged_SF_new_version.tex:L6148–6154`, following the approved
internal project record `#rphi-wave-identity`. No incoming charge or mass equation enters.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- The covariant derivative of a product with a real expansion follows
from its two ordinary sectional derivatives. This specializes the landed
algebraic `rφ` core to complex fields, with the connection term displayed.
There are no estimate constants or incoming constraint assumptions. -/
theorem hasDerivWithinAt_wave_product_of_transport
    {s : Set ℝ} {u : ℝ} {L : ℝ → ℝ} {H : ℝ → ℂ}
    (r nu mu q e A : ℝ) (phi y : ℂ)
    (hr : r ≠ 0) (hd : 1 - mu ≠ 0) (hHval : H u = phi + y)
    (hL : HasDerivWithinAt L
      (nu * L u * (mu - q ^ 2 / r ^ 2) / (r * (1 - mu))) s u)
    (hH : HasDerivWithinAt H
      (-((nu : ℂ) / r) *
        (((mu : ℂ) - (q : ℂ) ^ 2 / (r : ℂ) ^ 2) / (1 - (mu : ℂ)) * y +
          I * e * q / (1 - (mu : ℂ)) * phi) - I * e * A * H u) s u) :
    HasDerivWithinAt (fun x => (L x : ℂ) * H x)
      (((nu : ℂ) * L u / ((1 - (mu : ℂ)) * (r : ℂ) ^ 2) *
          ((mu : ℂ) - (q : ℂ) ^ 2 / (r : ℂ) ^ 2 - I * e * q) * ((r : ℂ) * phi)) -
        I * e * A * ((L u : ℂ) * H u)) s u := by
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hdc : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hd
  have core := rphi_wave_identity_algebra (r : ℂ) (L u : ℂ) (nu : ℂ)
    (mu : ℂ) (q : ℂ) (I * e) phi y hrc hdc
  dsimp only at core
  convert hL.ofReal_comp.mul hH using 1
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow, hHval]
  linear_combination -core

/-- [node restart-sec-independent-null-construction#rphi-wave-identity]
The actual outgoing derivative of `rφ` satisfies the incoming charged wave
identity at a Picard fixed point (`charged_SF_new_version.tex:L6148–6154`). The incoming
section ends strictly before `v`, so its outgoing sections are nondegenerate
even when `v` is the upper cone endpoint. The coefficient continuity inputs
come from radial reconstruction. Both Picard equations are explicit and S1
is retained on all prefixes. There are no estimate constants. -/
theorem rphi_wave_identity_of_picard
    {e c U b u v l κ : ℝ} {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ}
    (hl : 0 < l) (hκ : 0 < κ) (hu : u ∈ Icc c U) (hUv : U < v) (hvb : v ≤ b)
    (cl : ∀ x ∈ Icc c U, ContinuousOn (lam x) (Icc x b))
    (ch : ∀ x ∈ Icc c U, ContinuousOn (hh x) (Icc x b))
    (hlo : ∀ x ∈ Icc c U, ∀ s ∈ Icc x b, l ≤ lam x s)
    (hgap : ∀ x ∈ Icc c U, ∀ s ∈ Icc x b, κ ≤ 1 - Recon.mu e lam hh x s)
    (cG : ContinuousOn (fun x =>
      Recon.nu e lam hh x v / Recon.r lam x v * Recon.z e lam hh x v) (Icc c U))
    (cA : ContinuousOn (fun x => Recon.A e lam hh x v) (Icc c U))
    (cP : ContinuousOn (fun x =>
      (((-Recon.nu e lam hh x v / Recon.r lam x v : ℝ) : ℂ) *
        ((Recon.z e lam hh x v : ℂ) * Recon.ratio lam hh x v +
          I * e * Recon.Q e lam hh x v * Recon.phi lam hh x v /
            (1 - (Recon.mu e lam hh x v : ℂ))))) (Icc c U))
    (hL : ∀ x ∈ Icc c U, Recon.picardLam e lam hh c lam₀ x v = lam x v)
    (hH : ∀ x ∈ Icc c U, Recon.picardH e lam hh c h₀ x v = hh x v) :
    HasDerivWithinAt
      (fun x => derivWithin (fun s => (Recon.r lam x s : ℂ) * Recon.phi lam hh x s)
        (Icc x b) v)
      (((Recon.nu e lam hh u v : ℂ) * lam u v /
          ((1 - (Recon.mu e lam hh u v : ℂ)) * (Recon.r lam u v : ℂ) ^ 2) *
          ((Recon.mu e lam hh u v : ℂ) - (Recon.Q e lam hh u v : ℂ) ^ 2 /
            (Recon.r lam u v : ℂ) ^ 2 - I * e * Recon.Q e lam hh u v) *
          ((Recon.r lam u v : ℂ) * Recon.phi lam hh u v)) -
        I * e * Recon.A e lam hh u v * ((lam u v : ℂ) * hh u v)) (Icc c U) u := by
  have huv : u < v := hu.2.trans_lt hUv
  have hr : Recon.r lam u v ≠ 0 :=
    (Recon.r_pos hl huv ((cl u hu).mono (Icc_subset_Icc le_rfl hvb))
      (fun s hs => hlo u hu s ⟨hs.1, hs.2.trans hvb⟩)).ne'
  have hd : 1 - Recon.mu e lam hh u v ≠ 0 :=
    (hκ.trans_le (hgap u hu v ⟨huv.le, hvb⟩)).ne'
  have dL := Recon.hasDerivWithinAt_lam_of_picardLam cG hu hL
  have dH := Recon.hasDerivWithinAt_h_of_picardH cA cP hu hH
  have dL' : HasDerivWithinAt (fun x => lam x v)
      (Recon.nu e lam hh u v * lam u v *
        (Recon.mu e lam hh u v - Recon.Q e lam hh u v ^ 2 / Recon.r lam u v ^ 2) /
          (Recon.r lam u v * (1 - Recon.mu e lam hh u v))) (Icc c U) u := by
    convert dL using 1
    dsimp only [Recon.z]
    field_simp [hr, hd]
  have dH' : HasDerivWithinAt (fun x => hh x v)
      (-((Recon.nu e lam hh u v : ℂ) / Recon.r lam u v) *
        (((Recon.mu e lam hh u v : ℂ) - (Recon.Q e lam hh u v : ℂ) ^ 2 /
          (Recon.r lam u v : ℂ) ^ 2) / (1 - (Recon.mu e lam hh u v : ℂ)) *
          Recon.ratio lam hh u v + I * e * Recon.Q e lam hh u v /
            (1 - (Recon.mu e lam hh u v : ℂ)) * Recon.phi lam hh u v) -
        I * e * Recon.A e lam hh u v * hh u v) (Icc c U) u := by
    convert dH using 1
    simp only [Recon.z, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have hval : hh u v = Recon.phi lam hh u v + Recon.ratio lam hh u v := by
    simp only [Recon.ratio]
    ring
  have dw := hasDerivWithinAt_wave_product_of_transport
    (u := u) (s := Icc c U) (L := fun x => lam x v) (H := fun x => hh x v)
    (Recon.r lam u v) (Recon.nu e lam hh u v) (Recon.mu e lam hh u v)
    (Recon.Q e lam hh u v) e (Recon.A e lam hh u v)
    (Recon.phi lam hh u v) (Recon.ratio lam hh u v) hr hd hval dL' dH'
  have heq (x : ℝ) (hx : x ∈ Icc c U) :
      derivWithin (fun s => (Recon.r lam x s : ℂ) * Recon.phi lam hh x s)
        (Icc x b) v = (lam x v : ℂ) * hh x v :=
    (Recon.hasDerivWithinAt_r_mul_phi hl (cl x hx) (ch x hx) (hlo x hx)
      ⟨(hx.2.trans_lt hUv).le, hvb⟩).derivWithin
        (uniqueDiffOn_Icc ((hx.2.trans_lt hUv).trans_le hvb) v
          ⟨(hx.2.trans_lt hUv).le, hvb⟩)
  exact dw.congr heq (heq u hu)

end EmcsfAcExtension.Local.Null
