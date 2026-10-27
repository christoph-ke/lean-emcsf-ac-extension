module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.DefectsFlux
import EmcsfAcExtension.Local.Construction.FullSystemMixed

/-! # Transport of the actual incoming mass defect

internal project record (30), (33)–(34). Differentiated outgoing primitives supply
the mixed mass derivative. The incoming mass and charge derivatives remain
arbitrary and are written as their prescribed flux plus their actual defect.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- The actual mass defect satisfies the triangular outgoing transport,
with coefficient `-‖θ‖²/(λr)` and charge coefficient `λQ/r²`. All inputs
are C¹ fields, the proved C¹ outgoing mass source, and previously recovered
outgoing/geometric/wave equations. Neither incoming constraint is assumed.
There are no estimate constants and no C² premise. -/
theorem defect_transport_mass_of_c1_sources {a b c e : ℝ} {S : Fields}
    (hac : a < c) (hcb : c ≤ b)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cl : ContDiffOn ℝ 1 (Function.uncurry S.lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cMV : ContDiffOn ℝ 1 (Function.uncurry S.mV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hr : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 → S.r p.1 p.2 ≠ 0)
    (hl : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, S.lam p.1 p.2 ≠ 0)
    (hn : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, S.nu p.1 p.2 ≠ 0)
    (hd : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, 1 - S.mu p.1 p.2 ≠ 0)
    (hru : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.r p.1 p.2 = S.nu p.1 p.2)
    (hrv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.r p.1 p.2 = S.lam p.1 p.2)
    (hlu : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.lam p.1 p.2 = S.rUV p.1 p.2)
    (hnv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.nu p.1 p.2 = S.rUV p.1 p.2)
    (hmv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.m p.1 p.2 = S.mV p.1 p.2)
    (hQv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.Q p.1 p.2 = S.QV e p.1 p.2)
    (htu : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hxv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.xi p.1 p.2 = S.xiV e p.1 p.2) :
    ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u)
        (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) *
            defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u v +
          (S.lam u v * S.Q u v / S.r u v ^ 2) *
            defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u v) v := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
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
  let E : ℂ := defectM D S u v
  let Z : ℂ := defectQ e D S u v
  let H := 1 - M
  let B := M - Q ^ 2 / R ^ 2
  let UV := N * L * B / (R * H)
  let mU := H * Xb * X / (2 * N) + Q ^ 2 * N / (2 * R ^ 2)
  let mV := H * Tb * T / (2 * L) + Q ^ 2 * L / (2 * R ^ 2)
  let qU := -g * R / 2 * (Pb * X - P * Xb)
  let qV := g * R / 2 * (Pb * T - P * Tb)
  let HU := (M * N - 2 * (mU + E)) / R
  let HV := (M * L - 2 * mV) / R
  let tU := -L * X / R - g * Q * P * N * L / (H * R)
  let tbU := -L * Xb / R + g * Q * Pb * N * L / (H * R)
  let xV := -N * T / R + g * Q * P * N * L / (H * R)
  let xbV := -N * Tb / R - g * Q * Pb * N * L / (H * R)
  let mvU := (HU * Tb * T + H * (tbU * T + Tb * tU)) / (2 * L) -
    H * Tb * T * UV / (2 * L ^ 2) + Q * (qU + Z) * L / R ^ 2 +
    Q ^ 2 * UV / (2 * R ^ 2) - Q ^ 2 * L * N / R ^ 3
  let muV := (HV * Xb * X + H * (xbV * X + Xb * xV)) / (2 * N) -
    H * Xb * X * UV / (2 * N ^ 2) + Q * qV * N / R ^ 2 +
    Q ^ 2 * UV / (2 * R ^ 2) - Q ^ 2 * N * L / R ^ 3
  have hrR := hr (u, v) hp hv.1
  have hrC : (S.r u v : ℂ) ≠ 0 := by exact_mod_cast hrR
  have hlC : (S.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl (u, v) hp
  have hnC : (S.nu u v : ℂ) ≠ 0 := by exact_mod_cast hn (u, v) hp
  have hdC : 1 - (S.mu u v : ℂ) ≠ 0 := by exact_mod_cast hd (u, v) hp
  have hsreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  have hsI : star (I : ℂ) = -I := by simp
  have hMU : (S.mU u v : ℂ) = mU := by
    simpa only [Fields.mU, Complex.ofReal_sub, Complex.ofReal_one, mU, H, R, N, Q, M,
      X, Xb, starRingEnd_apply] using!
      mass_flux_eq_complex (1 - S.mu u v) (S.nu u v) (S.Q u v) (S.r u v) (S.xi u v)
  have hMV : (S.mV u v : ℂ) = mV := by
    simpa only [Fields.mV, Complex.ofReal_sub, Complex.ofReal_one, mV, H, R, L, Q, M,
      T, Tb, starRingEnd_apply] using!
      mass_flux_eq_complex (1 - S.mu u v) (S.lam u v) (S.Q u v) (S.r u v) (S.theta u v)
  have hQV : (S.QV e u v : ℂ) = qV := by
    simpa only [Fields.QV, qV, R, g, P, Pb, T, Tb, starRingEnd_apply] using!
      negative_current_eq_complex e (S.r u v) (S.phi u v) (S.theta u v)
  have hQU : (S.QU e u v : ℂ) = qU := by
    have h := congrArg Neg.neg (negative_current_eq_complex e (S.r u v) (S.phi u v) (S.xi u v))
    simp only [Complex.ofReal_neg, neg_neg] at h
    simpa only [Fields.QU, qU, R, g, P, Pb, X, Xb, starRingEnd_apply, neg_mul, neg_div] using! h
  have hE : (pdU (E := ℝ) D S.m u v : ℂ) = mU + E := by
    dsimp only [E, defectM]
    push_cast
    rw [← hMU]
    ring
  have hZ : (pdU (E := ℝ) D S.Q u v : ℂ) = qU + Z := by
    dsimp only [Z, defectQ]
    push_cast
    rw [← hQU]
    ring
  have drU := hasDerivWithinAt_pdU cr hp hsU
  rw [hru (u, v) hp hv.1] at drU
  have drV := hasDerivWithinAt_pdV cr hp hsV
  rw [hrv (u, v) hp hv.1] at drV
  have dLU0 := (hasDerivWithinAt_pdU cl hp hsU).ofReal_comp
  rw [hlu (u, v) hp hv.1] at dLU0
  have dLU : HasDerivWithinAt (fun x => (S.lam x v : ℂ)) UV (Icc a (min c v)) u := by
    convert dLU0 using 1
    dsimp only [UV, B, H, R, L, N, M, Q, Fields.rUV]
    push_cast
    field_simp [hrC, hdC]
  have dNV0 := (hasDerivWithinAt_pdV cn hp hsV).ofReal_comp
  rw [hnv (u, v) hp hv.1] at dNV0
  have dNV : HasDerivWithinAt (fun y => (S.nu u y : ℂ)) UV (Icc u b) v := by
    convert dNV0 using 1
    dsimp only [UV, B, H, R, L, N, M, Q, Fields.rUV]
    push_cast
    field_simp [hrC, hdC]
  have dmU := hasDerivWithinAt_pdU cm hp hsU
  have dHU0 := (hasDerivWithinAt_const u (Icc a (min c v)) (1 : ℂ)).sub
    (((dmU.const_mul (2 : ℝ)).div drU hrR).ofReal_comp)
  change HasDerivWithinAt (fun x => 1 - (S.mu x v : ℂ)) _ (Icc a (min c v)) u at dHU0
  have dHU : HasDerivWithinAt (fun x => 1 - (S.mu x v : ℂ)) HU (Icc a (min c v)) u := by
    convert dHU0 using 1
    dsimp only [HU]
    rw [← hE]
    dsimp only [M, N, R, Fields.mu]
    push_cast
    field_simp [hrC]
    ring
  have dmV := hasDerivWithinAt_pdV cm hp hsV
  rw [hmv (u, v) hp hv.1] at dmV
  have dHV0 := (hasDerivWithinAt_const v (Icc u b) (1 : ℂ)).sub
    (((dmV.const_mul (2 : ℝ)).div drV hrR).ofReal_comp)
  change HasDerivWithinAt (fun y => 1 - (S.mu u y : ℂ)) _ (Icc u b) v at dHV0
  have dHV : HasDerivWithinAt (fun y => 1 - (S.mu u y : ℂ)) HV (Icc u b) v := by
    convert dHV0 using 1
    dsimp only [HV]
    rw [← hMV]
    dsimp only [M, L, R, Fields.mu]
    push_cast
    field_simp [hrC]
    ring
  have dQU := (hasDerivWithinAt_pdU cQ hp hsU).ofReal_comp
  rw [hZ] at dQU
  have dQV := (hasDerivWithinAt_pdV cQ hp hsV).ofReal_comp
  rw [hQv (u, v) hp hv.1, hQV] at dQV
  have dTU0 := hasDerivWithinAt_pdU ct hp hsU
  rw [htu (u, v) hp hv.1] at dTU0
  have dTU : HasDerivWithinAt (fun x => S.theta x v)
      (-g * (S.A u v : ℂ) * T + tU) (Icc a (min c v)) u := by
    convert dTU0 using 1
    dsimp only [g, T, tU, R, L, N, H, M, Q, P, X, Fields.thetaU, Fields.waveSource]
    ring
  have dTbU : HasDerivWithinAt (fun x => star (S.theta x v))
      (g * (S.A u v : ℂ) * Tb + tbU) (Icc a (min c v)) u := by
    convert dTU.star using 1
    simp only [tU, tbU, R, L, N, H, M, Q, g, P, Pb, X, Xb, T, Tb,
      star_add, star_sub, star_mul, star_div₀, star_neg, star_one, hsreal, hsI]
    field_simp [hrC, hdC]
    ring
  have dXV0 := hasDerivWithinAt_pdV cx hp hsV
  rw [hxv (u, v) hp hv.1] at dXV0
  have dXV : HasDerivWithinAt (S.xi u) xV (Icc u b) v := by
    convert dXV0 using 1
    dsimp only [xV, R, L, N, H, M, Q, g, P, T, Fields.xiV, Fields.waveSource]
    ring
  have dXbV : HasDerivWithinAt (fun y => star (S.xi u y)) xbV (Icc u b) v := by
    convert dXV.star using 1
    simp only [xV, xbV, R, L, N, H, M, Q, g, P, Pb, T, Tb,
      star_add, star_sub, star_mul, star_div₀, star_neg, star_one, hsreal, hsI]
    field_simp [hrC, hdC]
    ring
  have dmVU : HasDerivWithinAt (fun x => (S.mV x v : ℂ)) mvU (Icc a (min c v)) u := by
    have hjet := hasDerivWithinAt_mass_flux (x := u) (s := Icc a (min c v))
      (R := fun x => (S.r x v : ℂ)) (L := fun x => (S.lam x v : ℂ))
      (H := fun x => 1 - (S.mu x v : ℂ)) (Q := fun x => (S.Q x v : ℂ))
      (T := fun x => S.theta x v) (Tb := fun x => star (S.theta x v))
      hrC hlC drU.ofReal_comp dLU dHU dQU dTU dTbU
    have he (x : ℝ) : (S.mV x v : ℂ) =
        (1 - (S.mu x v : ℂ)) * star (S.theta x v) * S.theta x v / (2 * (S.lam x v : ℂ)) +
          (S.Q x v : ℂ) ^ 2 * S.lam x v / (2 * (S.r x v : ℂ) ^ 2) := by
      simpa only [Fields.mV, Complex.ofReal_sub, Complex.ofReal_one, starRingEnd_apply] using!
        mass_flux_eq_complex (1 - S.mu x v) (S.lam x v) (S.Q x v) (S.r x v) (S.theta x v)
    convert hjet.congr (fun x _ => he x) (he u) using 1
    dsimp only [mvU]
    ring
  have huniq := uniqueDiffOn_Icc (lt_min hac (hu.1.trans_lt hv.1)) u
    ⟨hu.1, le_min hu.2 hv.1.le⟩
  have hMVjet : (pdU (E := ℝ) D S.mV u v : ℂ) = mvU :=
    (((hasDerivWithinAt_pdU cMV hp hsU).ofReal_comp).derivWithin huniq).symm.trans
      (dmVU.derivWithin huniq)
  have dW := (hasDerivAt_pdU_of_pdV_on_wedge_off_axis hac hcb cm cMV hmv hu hv.1 hv.2).ofReal_comp
  rw [hMVjet] at dW
  have dmUV : HasDerivWithinAt (fun y => (S.mU u y : ℂ)) muV (Icc u b) v := by
    have hjet := hasDerivWithinAt_mass_flux (x := v) (s := Icc u b)
      (R := fun y => (S.r u y : ℂ)) (L := fun y => (S.nu u y : ℂ))
      (H := fun y => 1 - (S.mu u y : ℂ)) (Q := fun y => (S.Q u y : ℂ))
      (T := S.xi u) (Tb := fun y => star (S.xi u y)) hrC hnC drV.ofReal_comp dNV dHV dQV dXV dXbV
    have he (y : ℝ) : (S.mU u y : ℂ) =
        (1 - (S.mu u y : ℂ)) * star (S.xi u y) * S.xi u y / (2 * (S.nu u y : ℂ)) +
          (S.Q u y : ℂ) ^ 2 * S.nu u y / (2 * (S.r u y : ℂ) ^ 2) := by
      simpa only [Fields.mU, Complex.ofReal_sub, Complex.ofReal_one, starRingEnd_apply] using!
        mass_flux_eq_complex (1 - S.mu u y) (S.nu u y) (S.Q u y) (S.r u y) (S.xi u y)
    convert hjet.congr (fun y _ => he y) (he v) using 1
  have halg : mvU - muV = -(Tb * T / (L * R)) * E + L * Q / R ^ 2 * Z :=
    defect_transport_mass_algebra R L N M Q g P Pb T Tb X Xb E Z hrC hlC hnC hdC
  have hcoef : -(Tb * T / (L * R)) * E + L * Q / R ^ 2 * Z =
      ((-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * defectM D S u v +
        (S.lam u v * S.Q u v / S.r u v ^ 2) * defectQ e D S u v : ℝ) : ℂ) := by
    dsimp only [Tb, T, L, R, Q, E, Z]
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have deC : HasDerivAt (fun y => (defectM D S u y : ℂ))
      ((-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * defectM D S u v +
        (S.lam u v * S.Q u v / S.r u v ^ 2) * defectQ e D S u v : ℝ) : ℂ) v := by
    convert dW.sub (dmUV.hasDerivAt (Icc_mem_nhds hv.1 hv.2)) using 1
    · funext y
      simp only [defectM, Complex.ofReal_sub, Pi.sub_apply, D]
    · exact (halg.trans hcoef).symm
  simpa only [Function.comp_apply, Complex.ofReal_re] using!
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt v deC)

end EmcsfAcExtension.Local.Null
