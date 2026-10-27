module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Construction.WaveSystemFirstOrder
public import EmcsfAcExtension.Local.Construction.FullSystemPartialRules
public import EmcsfAcExtension.Local.Construction.FullSystemRegularity

/-! # The first-order wave system before incoming-jet regularity

internal project record (23)–(25). The temporary incoming scalar jet is continuous;
its outgoing derivative is supplied by the actual `rφ` primitive. Its
incoming C¹ regularity is recovered later from the `b` primitive (27).
-/

public section

open Set Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- The actual first derivatives of the rφ primitive recover the two
first-order scalar transports. The temporary incoming jet is defined as
`r D_u φ`; only its outgoing derivative is claimed at this stage.
All hypotheses are first regularity and previously recovered equations.
No second derivative of φ or incoming Maxwell/mass constraint is assumed. -/
theorem first_order_wave_system_of_c1_primitives {a b c e : ℝ} {S : Fields}
    (hac : a < c) (hcb : c ≤ b)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cl : ContDiffOn ℝ 1 (Function.uncurry S.lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContDiffOn ℝ 1 (Function.uncurry S.A) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hr : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 → S.r p.1 p.2 ≠ 0)
    (hd : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, 1 - S.mu p.1 p.2 ≠ 0)
    (hr0 : ∀ t ∈ Icc a c, S.r t t = 0)
    (hru : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.r p.1 p.2 = S.nu p.1 p.2)
    (hlu : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.lam p.1 p.2 = S.rUV p.1 p.2)
    (hnv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.nu p.1 p.2 = S.rUV p.1 p.2)
    (hpv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.phi p.1 p.2 = S.phiV p.1 p.2)
    (hAv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.A p.1 p.2 = S.AV p.1 p.2)
    (hNv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
        (fun u v => (S.r u v : ℂ) * S.phi u v) p.1 p.2 =
        (S.lam p.1 p.2 : ℂ) * S.phi p.1 p.2 + S.theta p.1 p.2)
    (hW : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
        (fun u v => (S.lam u v : ℂ) * S.phi u v + S.theta u v) p.1 p.2 =
        (S.nu p.1 p.2 : ℂ) * S.lam p.1 p.2 /
            ((1 - (S.mu p.1 p.2 : ℂ)) * (S.r p.1 p.2 : ℂ) ^ 2) *
          ((S.mu p.1 p.2 : ℂ) - (S.Q p.1 p.2 : ℂ) ^ 2 / (S.r p.1 p.2 : ℂ) ^ 2 -
            I * e * S.Q p.1 p.2) * ((S.r p.1 p.2 : ℂ) * S.phi p.1 p.2) -
          I * e * S.A p.1 p.2 * ((S.lam p.1 p.2 : ℂ) * S.phi p.1 p.2 + S.theta p.1 p.2)) :
    ∃ X : ℝ → ℝ → ℂ,
      ContinuousOn (Function.uncurry X) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      (∀ t ∈ Icc a c, X t t = 0) ∧
      (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        X p.1 p.2 = (S.r p.1 p.2 : ℂ) *
          (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.phi p.1 p.2 +
            I * e * S.A p.1 p.2 * S.phi p.1 p.2)) ∧
      (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
        pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.theta p.1 p.2 =
          -(I * e * S.A p.1 p.2 * S.theta p.1 p.2) -
            (S.lam p.1 p.2 : ℂ) * X p.1 p.2 / S.r p.1 p.2 -
            I * e * S.Q p.1 p.2 * S.phi p.1 p.2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
              ((1 - (S.mu p.1 p.2 : ℂ)) * S.r p.1 p.2)) ∧
      (∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
        HasDerivAt (X u) (-((S.nu u v : ℂ) * S.theta u v / S.r u v) +
          I * e * S.Q u v * S.phi u v * S.nu u v * S.lam u v /
            ((1 - (S.mu u v : ℂ)) * S.r u v)) v) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let N (u v : ℝ) := (S.r u v : ℂ) * S.phi u v
  let J (u v : ℝ) := (S.lam u v : ℂ) * S.phi u v + S.theta u v
  let X (u v : ℝ) := (S.r u v : ℂ) * (pdU D S.phi u v + I * e * S.A u v * S.phi u v)
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have crC : ContDiffOn ℝ 1 (Function.uncurry (fun u v => (S.r u v : ℂ))) D := by
    simpa only [Function.uncurry, Function.comp_apply] using!
      Complex.ofRealCLM.contDiff.comp_contDiffOn cr
  have clC : ContDiffOn ℝ 1 (Function.uncurry (fun u v => (S.lam u v : ℂ))) D := by
    simpa only [Function.uncurry, Function.comp_apply] using!
      Complex.ofRealCLM.contDiff.comp_contDiffOn cl
  have cN : ContDiffOn ℝ 1 (Function.uncurry N) D := crC.mul cp
  have cJ : ContDiffOn ℝ 1 (Function.uncurry J) D := (clC.mul cp).add ct
  have cX : ContinuousOn (Function.uncurry X) D := crC.continuousOn.mul
    ((continuousOn_pdU cp hD).add
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn cA.continuousOn)).mul
        cp.continuousOn))
  have hrep (p : ℝ × ℝ) (hp : p ∈ D) : X p.1 p.2 =
      pdU D N p.1 p.2 - (S.nu p.1 p.2 : ℂ) * S.phi p.1 p.2 +
        I * e * S.A p.1 p.2 * N p.1 p.2 := by
    change _ = pdU D (fun u v => (S.r u v : ℂ) * S.phi u v) p.1 p.2 - _ + _
    rw [pdU_mul hD crC cp hp, pdU_ofReal hD cr hp, hru p hp]
    dsimp only [X, N]
    ring
  refine ⟨X, cX, (fun t ht => by simp [X, hr0 t ht]), (fun _ _ => rfl), ?_, ?_⟩
  · intro p hp huv
    have hs : MapsTo (fun u => (u, p.2)) (Icc a (min c p.2)) D :=
      fun u hu => ⟨⟨hu.1, (le_min_iff.mp hu.2).2, hp.1.2.2⟩, (le_min_iff.mp hu.2).1⟩
    have dJ := hasDerivWithinAt_pdU cJ hp hs
    rw [hW p hp huv] at dJ
    have dL := hasDerivWithinAt_pdU cl hp hs
    rw [hlu p hp huv] at dL
    have dP : HasDerivWithinAt (fun u => S.phi u p.2)
        (X p.1 p.2 / (S.r p.1 p.2 : ℂ) - I * e * S.A p.1 p.2 * S.phi p.1 p.2)
        (Icc a (min c p.2)) p.1 := by
      convert hasDerivWithinAt_pdU cp hp hs using 1
      dsimp only [X]
      have hrC : (S.r p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast hr p hp huv
      field_simp [hrC]
      dsimp only [D]
      ring
    have dt := hasDerivWithinAt_theta_of_wave_primitive (S.r p.1 p.2) (S.nu p.1 p.2)
      (S.mu p.1 p.2) (S.Q p.1 p.2) e (S.A p.1 p.2) (S.theta p.1 p.2) (X p.1 p.2)
      (hr p hp huv) (hd p hp) rfl dJ dL dP
    have dt' : HasDerivWithinAt (fun u => S.theta u p.2) _ (Icc a (min c p.2)) p.1 :=
      dt.congr (fun u _ => by dsimp only [J]; ring) (by dsimp only [J]; ring)
    have ha : a < min c p.2 := lt_min hac (hp.1.1.trans_lt huv)
    exact ((hasDerivWithinAt_pdU ct hp hs).derivWithin
      (uniqueDiffOn_Icc ha p.1 ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩)).symm.trans
        (dt'.derivWithin (uniqueDiffOn_Icc ha p.1 ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩))
  · intro u hu v hv
    have hp : (u, v) ∈ D := ⟨⟨hu.1, hv.1.le, hv.2.le⟩, hu.2⟩
    have hs : MapsTo (fun v => (u, v)) (Icc u b) D :=
      fun v hv => ⟨⟨hu.1, hv.1, hv.2⟩, hu.2⟩
    have dW := hasDerivAt_pdU_of_pdV_on_wedge hac hcb cN cJ hNv hu hv.1 hv.2
    rw [hW (u, v) hp hv.1] at dW
    have dN := (hasDerivWithinAt_pdV cN hp hs).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    rw [hNv (u, v) hp] at dN
    have dV := (hasDerivWithinAt_pdV cn hp hs).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    rw [hnv (u, v) hp hv.1] at dV
    have dP := (hasDerivWithinAt_pdV cp hp hs).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    rw [hpv (u, v) hp hv.1] at dP
    have dA := (hasDerivWithinAt_pdV cA hp hs).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    rw [hAv (u, v) hp hv.1] at dA
    have dx := hasDerivAt_xi_of_wave_primitive
      (W := pdU D N u) (N := N u) (P := S.phi u) (V := S.nu u) (A := S.A u)
      (S.r u v) (S.lam u v) (S.mu u v) (S.Q u v) e
      (S.theta u v) (J u v) (hr (u, v) hp hv.1) (hd (u, v) hp) rfl rfl dW dN dV dP dA
    apply dx.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds hv.1 hv.2] with s hs'
    exact hrep (u, s) (hs hs')

end EmcsfAcExtension.Local.Null
