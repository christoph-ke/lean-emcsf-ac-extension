module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.DefectsFlux
import EmcsfAcExtension.Local.Construction.FullSystemMixed

/-! # Transport of the actual incoming Maxwell defect

internal project record (30)–(32). The outgoing derivative of `Q_u` is obtained
from the C¹ outgoing charge source by its primitive. No incoming Maxwell
constraint and no second derivative of Q are hypotheses.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- The actual Maxwell defect has zero outgoing derivative. The inputs are
C¹ primary fields and the previously recovered geometric and wave equations.
The only differentiated mixed quantity is supplied by the outgoing Q
primitive. There are no estimate constants or incoming charge assumptions. -/
theorem defect_transport_charge_of_c1_sources {a b c e : ℝ} {S : Fields}
    (hac : a < c) (hcb : c ≤ b)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hr : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 → S.r p.1 p.2 ≠ 0)
    (hd : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, 1 - S.mu p.1 p.2 ≠ 0)
    (hru : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.r p.1 p.2 = S.nu p.1 p.2)
    (hrv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.r p.1 p.2 = S.lam p.1 p.2)
    (hQv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.Q p.1 p.2 = S.QV e p.1 p.2)
    (hpu : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.phi p.1 p.2 = S.phiU e p.1 p.2)
    (hpv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.phi p.1 p.2 = S.phiV p.1 p.2)
    (htu : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hxv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.xi p.1 p.2 = S.xiV e p.1 p.2) :
    ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u) 0 v := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  have cQV : ContDiffOn ℝ 1 (Function.uncurry (S.QV e)) D := by
    simpa only [Fields.QV, Function.uncurry, Function.comp_apply] using!
      (((contDiffOn_const (c := e)).mul cr).mul
        (Complex.imCLM.contDiff.comp_contDiffOn
          ((Complex.conjCLE.contDiff.comp_contDiffOn cp).mul ct))).neg
  intro u hu v hv
  have hp : (u, v) ∈ D := ⟨⟨hu.1, hv.1.le, hv.2.le⟩, hu.2⟩
  have hsU : MapsTo (fun x => (x, v)) (Icc a (min c v)) D :=
    fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hv.2.le⟩, (le_min_iff.mp hx.2).1⟩
  have hsV : MapsTo (fun y => (u, y)) (Icc u b) D :=
    fun y hy => ⟨⟨hu.1, hy.1, hy.2⟩, hu.2⟩
  let R : ℂ := S.r u v
  let L : ℂ := S.lam u v
  let N : ℂ := S.nu u v
  let M : ℂ := S.mu u v
  let Q : ℂ := S.Q u v
  let g : ℂ := I * e
  let P := S.phi u v
  let Pb := star P
  let T := S.theta u v
  let Tb := star T
  let X := S.xi u v
  let Xb := star X
  let H := 1 - M
  let tU := -L * X / R - g * Q * P * N * L / (H * R)
  let tbU := -L * Xb / R + g * Q * Pb * N * L / (H * R)
  let xV := -N * T / R + g * Q * P * N * L / (H * R)
  let xbV := -N * Tb / R - g * Q * Pb * N * L / (H * R)
  let qvU := g / 2 * (N * (Pb * T - P * Tb) +
    R * (Xb / R * T + Pb * tU - X / R * Tb - P * tbU))
  let quV := -g / 2 * (L * (Pb * X - P * Xb) +
    R * (Tb / R * X + Pb * xV - T / R * Xb - P * xbV))
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hr (u, v) hp hv.1
  have hdC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hd (u, v) hp
  have hsreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  have hsI : star (I : ℂ) = -I := by simp
  have drU := hasDerivWithinAt_pdU cr hp hsU
  rw [hru (u, v) hp hv.1] at drU
  have dpU := hasDerivWithinAt_pdU cp hp hsU
  rw [hpu (u, v) hp hv.1] at dpU
  have dtU := hasDerivWithinAt_pdU ct hp hsU
  rw [htu (u, v) hp hv.1] at dtU
  have dqVU : HasDerivWithinAt (fun x => (S.QV e x v : ℂ)) qvU (Icc a (min c v)) u := by
    have hjet := hasDerivWithinAt_charge_flux g drU.ofReal_comp dpU dpU.star dtU dtU.star
    have he (x : ℝ) : (S.QV e x v : ℂ) = g / 2 *
        ((S.r x v : ℂ) * (star (S.phi x v) * S.theta x v - S.phi x v * star (S.theta x v))) := by
      dsimp only [Fields.QV, g]
      rw [negative_current_eq_complex]
      simp only [starRingEnd_apply]
      ring
    have hjet' := hjet.congr (fun x _ => he x) (he u)
    convert hjet' using 1
    simp only [qvU, tU, tbU, R, L, N, M, Q, g, P, Pb, T, Tb, X, Xb, H,
      Fields.phiU, Fields.thetaU, Fields.waveSource,
      star_sub, star_mul, star_div₀, star_neg, star_one, hsreal, hsI]
    field_simp [hrC, hdC]
    ring
  have huniq := uniqueDiffOn_Icc (lt_min hac (hu.1.trans_lt hv.1)) u
    ⟨hu.1, le_min hu.2 hv.1.le⟩
  have hQVjet : (pdU (E := ℝ) D (S.QV e) u v : ℂ) = qvU :=
    (((hasDerivWithinAt_pdU cQV hp hsU).ofReal_comp).derivWithin huniq).symm.trans
      (dqVU.derivWithin huniq)
  have dW := (hasDerivAt_pdU_of_pdV_on_wedge_off_axis hac hcb cQ cQV hQv hu hv.1 hv.2).ofReal_comp
  rw [hQVjet] at dW
  have drV := hasDerivWithinAt_pdV cr hp hsV
  rw [hrv (u, v) hp hv.1] at drV
  have dpV := hasDerivWithinAt_pdV cp hp hsV
  rw [hpv (u, v) hp hv.1] at dpV
  have dxV := hasDerivWithinAt_pdV cx hp hsV
  rw [hxv (u, v) hp hv.1] at dxV
  have dqUV : HasDerivWithinAt (fun y => (S.QU e u y : ℂ)) quV (Icc u b) v := by
    have hjet := hasDerivWithinAt_charge_flux (-g) drV.ofReal_comp dpV dpV.star dxV dxV.star
    have he (y : ℝ) : (S.QU e u y : ℂ) = -g / 2 *
        ((S.r u y : ℂ) * (star (S.phi u y) * S.xi u y - S.phi u y * star (S.xi u y))) := by
      have h := congrArg Neg.neg (negative_current_eq_complex e (S.r u y) (S.phi u y) (S.xi u y))
      simp only [Complex.ofReal_neg, neg_neg] at h
      dsimp only [Fields.QU, g]
      rw [h]
      simp only [starRingEnd_apply]
      ring
    have hjet' := hjet.congr (fun y _ => he y) (he v)
    convert hjet' using 1
    simp only [quV, xV, xbV, R, L, N, M, Q, g, P, Pb, T, Tb, X, Xb, H,
      Fields.phiV, Fields.xiV, Fields.waveSource,
      star_add, star_sub, star_mul, star_div₀, star_neg, star_one, hsreal, hsI]
    field_simp [hrC, hdC]
    ring
  have halg : qvU - quV = 0 := defect_transport_charge_algebra
    R L N M Q g P Pb T Tb X Xb hrC hdC
  have dzC : HasDerivAt (fun y => (defectQ e D S u y : ℂ)) 0 v := by
    convert dW.sub (dqUV.hasDerivAt (Icc_mem_nhds hv.1 hv.2)) using 1
    · funext y
      simp only [defectQ, Complex.ofReal_sub, Pi.sub_apply, D]
    · exact halg.symm
  simpa only [Function.comp_apply, Complex.ofReal_re, map_zero] using!
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt v dzC)

end EmcsfAcExtension.Local.Null
