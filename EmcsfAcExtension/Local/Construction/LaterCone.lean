module

public import EmcsfAcExtension.Local.Construction.PicardMap
public import EmcsfAcExtension.Local.Construction.PicardShortConeContraction

/-! # Boundary identities for the incoming map on a later cone

The reconstruction definitions allow an arbitrary starting cone. The incoming
fibers solve their ODEs, take the prescribed initial values, and have vanishing
source coefficients at the axis. The uniform short-cone construction below supplies existence and
uniqueness
on the full axis triangle. The vertex and axis identities impose no future
axis trace or restriction on the initial outgoing derivative.
-/

public section

open Complex Set
open scoped ENNReal ContDiff

namespace EmcsfAcExtension.Local.Recon

variable (e : ℝ) (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ)

private theorem r_axis_aux (c : ℝ) : r lam c c = 0 := by simp [r]
private theorem phi_axis_aux (c : ℝ) : phi lam hh c c = hh c c := by simp [phi]
private theorem Q_axis_aux (c : ℝ) : Q e lam hh c c = 0 := by simp [Q]
private theorem m_axis_aux (c : ℝ) : m e lam hh c c = 0 := by simp [m]
private theorem mu_axis_aux (c : ℝ) : mu e lam hh c c = 0 := by simp [mu, r, m]
private theorem nu_axis_aux (c : ℝ) : nu e lam hh c c = -lam c c := by simp [nu]
private theorem A_axis_aux (c : ℝ) : A e lam hh c c = 0 := by simp [A]

/-- Reconstruction at a later cone's vertex has the regular-axis values.
This identity uses no future axis data and no incoming field equations. -/
theorem laterCone_reconstruction_vertex (c : ℝ) :
    r lam c c = 0 ∧ phi lam hh c c = hh c c ∧ Q e lam hh c c = 0 ∧
    m e lam hh c c = 0 ∧ mu e lam hh c c = 0 ∧
    nu e lam hh c c = -lam c c ∧ A e lam hh c c = 0 :=
  ⟨r_axis_aux lam c, phi_axis_aux lam hh c, Q_axis_aux e lam hh c,
    m_axis_aux e lam hh c, mu_axis_aux e lam hh c,
    nu_axis_aux e lam hh c, A_axis_aux e lam hh c⟩

/-- At the starting vertex both updates take precisely the prescribed cone
values, with no condition on either outgoing derivative. -/
theorem laterCone_picard_vertex (c : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ) :
    picardLam e lam hh c lam₀ c c = lam₀ c ∧
      picardH e lam hh c h₀ c c = h₀ c :=
  ⟨picardLam_initial e lam hh c lam₀ c, picardH_initial e lam hh c h₀ c⟩


end EmcsfAcExtension.Local.Recon

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The real incoming exponential formula with continuous clamped coefficients
on an entire incoming real line, based at `c`. -/
@[expose] noncomputable def picardLamFiber (ha : 0 ≤ a) (haL : a ≤ L) (lam0 : ℝ → ℝ)
    (G : PicardCarrier c a L ℝ) (v u : ℝ) : ℝ :=
  lam0 v * Real.exp (∫ s in c..u, G.1.1 (picardClamp ha haL (s, v)))
/-- The unitary incoming variation-of-constants formula with continuous
clamped real connection and complex scalar source, based at `c`. -/
@[expose] noncomputable def picardHFiber (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ) (h0 : ℝ → ℂ)
    (A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (v u : ℝ) : ℂ :=
  Complex.exp ((-(Complex.I * (e : ℂ))) * ((∫ s in c..u, A.1.1 (picardClamp ha haL (s, v)) : ℝ) :
      ℂ)) *
    (h0 v + ∫ s in c..u, Complex.exp ((-(-(Complex.I * (e : ℂ)))) *
      ((∫ t in c..s, A.1.1 (picardClamp ha haL (t, v)) : ℝ) : ℂ)) * P.1.1 (picardClamp ha haL (s,
          v)))

/-- The real incoming fiber solves `lambda_u=G*lambda` pointwise.
Only continuity of the old coefficient is used. -/
theorem picardLamFiber_hasDerivAt (ha : 0 ≤ a) (haL : a ≤ L) (lam0 : ℝ → ℝ)
    (G : PicardCarrier c a L ℝ) (v u : ℝ) :
    HasDerivAt (picardLamFiber ha haL lam0 G v)
      (G.1.1 (picardClamp ha haL (u, v)) * picardLamFiber ha haL lam0 G v u) u := by
  have hc : Continuous (fun s => G.1.1 (picardClamp ha haL (s, v))) :=
    G.1.1.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))
  have hd := ((hc.integral_hasStrictDerivAt c u).hasDerivAt.exp).const_mul (lam0 v)
  change HasDerivAt (fun y => lam0 v * Real.exp (∫ s in c..y, G.1.1 (picardClamp ha haL (s, v))))
    (G.1.1 (picardClamp ha haL (u, v)) * (lam0 v * Real.exp (∫ s in c..u, G.1.1 (picardClamp ha haL
        (s, v))))) u
  convert hd using 1
  ring

/-- The complex incoming fiber solves `h_u=-ie*A*h+P` pointwise.
Only continuity of the old coefficients is used; no derivative of the datum
in the outgoing direction is constrained. -/
theorem picardHFiber_hasDerivAt (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ) (h0 : ℝ → ℂ)
    (A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (v u : ℝ) :
    HasDerivAt (picardHFiber ha haL e h0 A P v)
      (-(Complex.I * (e : ℂ)) * (A.1.1 (picardClamp ha haL (u, v)) : ℂ) * picardHFiber ha haL e h0 A
          P v u +
        P.1.1 (picardClamp ha haL (u, v))) u := by
  let k : ℂ := -(Complex.I * (e : ℂ))
  let IA : ℝ → ℂ := fun s => ((∫ t in c..s, A.1.1 (picardClamp ha haL (t, v)) : ℝ) : ℂ)
  have hA : Continuous (fun s => A.1.1 (picardClamp ha haL (s, v))) :=
    A.1.1.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))
  have hP : Continuous (fun s => P.1.1 (picardClamp ha haL (s, v))) :=
    P.1.1.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))
  have hIA (s : ℝ) : HasDerivAt IA (A.1.1 (picardClamp ha haL (s, v)) : ℂ) s :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s (hA.integral_hasStrictDerivAt c s).hasDerivAt
  have hcIA : Continuous IA := continuous_iff_continuousAt.mpr (fun s => (hIA s).continuousAt)
  have hJ : Continuous (fun s => Complex.exp ((-k) * IA s) * P.1.1 (picardClamp ha haL (s, v))) :=
    (Complex.continuous_exp.comp (continuous_const.mul hcIA)).mul hP
  have hd := ((hIA u).const_mul k).cexp.fun_mul
    ((hJ.integral_hasStrictDerivAt c u).hasDerivAt.const_add (h0 v))
  have he : Complex.exp (k * IA u) * Complex.exp ((-k) * IA u) = 1 := by
    rw [←Complex.exp_add]
    have hz : k * IA u + (-k) * IA u = 0 := by ring
    rw [hz, Complex.exp_zero]
  change HasDerivAt (fun s => Complex.exp (k * IA s) *
    (h0 v + ∫ t in c..s, Complex.exp ((-k) * IA t) * P.1.1 (picardClamp ha haL (t, v))))
    (k * (A.1.1 (picardClamp ha haL (u, v)) : ℂ) *
      (Complex.exp (k * IA u) * (h0 v + ∫ t in c..u, Complex.exp ((-k) * IA t) * P.1.1 (picardClamp
          ha haL (t, v)))) +
      P.1.1 (picardClamp ha haL (u, v))) u
  convert hd using 1
  calc
    _ = k * (A.1.1 (picardClamp ha haL (u, v)) : ℂ) *
        (Complex.exp (k * IA u) * (h0 v + ∫ t in c..u, Complex.exp ((-k) * IA t) * P.1.1
            (picardClamp ha haL (t, v)))) +
        (Complex.exp (k * IA u) * Complex.exp ((-k) * IA u)) * P.1.1 (picardClamp ha haL (u, v)) :=
            by rw [he, one_mul]
    _ = _ := by ring
/-- The three incoming coefficients vanish at every axis point. This is the
regular-axis compatibility used by the later-cone map, with no prescribed
future axis values and no condition on the initial outgoing scalar derivative. -/
theorem picardSources_axis (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q)
    (p : PicardDomain c a L) (hp : p.1.2 = p.1.1) :
    (picardGRecon ha haL e ell kappa he hk z hl hgap).1.1 p = 0 ∧
      (picardARecon ha haL e ell kappa he hk z hl hgap).1.1 p = 0 ∧
      (picardPRecon ha haL e ell kappa he hk z hl hgap).1.1 p = 0 := by
  constructor
  · rw [picardGRecon_value]
    simp [hp, Recon.r_def]
  constructor
  · rw [picardARecon_value]
    simp [hp, Recon.a_def]
  · rw [picardPRecon_value]
    simp [hp, Recon.r_def]

/-- The real incoming fiber takes its prescribed starting-cone value. -/
@[simp] theorem picardLamFiber_initial (ha : 0 ≤ a) (haL : a ≤ L) (lam0 : ℝ → ℝ)
    (G : PicardCarrier c a L ℝ) (v : ℝ) : picardLamFiber ha haL lam0 G v c = lam0 v := by
  simp [picardLamFiber]

/-- The scalar incoming fiber takes its prescribed starting-cone value. -/
@[simp] theorem picardHFiber_initial (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ) (h0 : ℝ → ℂ)
    (A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (v : ℝ) :
    picardHFiber ha haL e h0 A P v c = h0 v := by
  simp [picardHFiber]

/-- The concrete coefficient-carrier update equals its real and complex
incoming ODE fibers at every wedge point. The only center premise fixes the
original cone datum; no future axis values are prescribed. -/
theorem picardCarrierUpdate_eq_fibers_of_center_values (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
    (lam0 : ℝ → ℝ) (h0 : ℝ → ℂ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam0 p.1.2, h0 p.1.2))
    (p : PicardDomain c a L) :
    (picardCarrierUpdate ha haL e ell κ he hκ center z hl hg).1.1 p =
      (picardLamFiber ha haL lam0 (picardGRecon ha haL e ell κ he hκ z hl hg) p.1.2 p.1.1,
        picardHFiber ha haL e h0 (picardARecon ha haL e ell κ he hκ z hl hg)
          (picardPRecon ha haL e ell κ he hκ z hl hg) p.1.2 p.1.1) := by
  let G := picardGRecon ha haL e ell κ he hκ z hl hg
  let A := picardARecon ha haL e ell κ he hκ z hl hg
  let P := picardPRecon ha haL e ell κ he hκ z hl hg
  change (picardIncomingCarrierUpdate ha haL e center G A P).1.1 p = _
  rw [picardIncomingCarrierUpdate_value, hc p]
  apply Prod.ext
  · rfl
  · change (picardIncomingPhase ha haL e A).1.1 p *
      (h0 p.1.2 + ∫ s in c..p.1.1,
        (picardIncomingPhase ha haL (-e) A).1.1 (picardClamp ha haL (s, p.1.2)) *
          P.1.1 (picardClamp ha haL (s, p.1.2))) = _
    unfold picardHFiber
    rw [picardIncomingPhase_value]
    congr 1
    · congr 1
      ring
    · congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [Set.uIcc_of_le p.2.1.1] at hs
      let q : PicardDomain c a L := ⟨(s, p.1.2),
        ⟨⟨hs.1, hs.2.trans p.2.1.2.1, p.2.1.2.2⟩, hs.2.trans p.2.2⟩⟩
      rw [show picardClamp ha haL (s, p.1.2) = q from picardClamp_coe ha haL q,
        picardIncomingPhase_value]
      congr 2
      push_cast
      ring

/-- The exact fixed-point integral equations imply the incoming differential
equations within every closed incoming section, with continuous coefficients
at its endpoints. This `_of_` helper assumes only the actual fixed-point
equations and the explicit S1 coefficient domain. -/
theorem picardFixedPoint_incoming_of_integral_equations (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
    (lam0 : ℝ → ℝ) (h0 : ℝ → ℂ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam0 p.1.2, h0 p.1.2))
    (hf : ∀ p : PicardDomain c a L, z.1.1 p = picardUpdate ha haL e lam0 h0 z p.1.1 p.1.2)
    (p : PicardDomain c a L) :
    HasDerivWithinAt (fun u => picardCandidateLam ha haL z u p.1.2)
      ((picardGRecon ha haL e ell κ he hκ z hl hg).1.1 p * (z.1.1 p).1)
      (Set.Icc c (min p.1.2 (c + a))) p.1.1 ∧
    HasDerivWithinAt (fun u => picardCandidateH ha haL z u p.1.2)
      (-(Complex.I * (e : ℂ)) * ((picardARecon ha haL e ell κ he hκ z hl hg).1.1 p : ℂ) *
        (z.1.1 p).2 + (picardPRecon ha haL e ell κ he hκ z hl hg).1.1 p)
      (Set.Icc c (min p.1.2 (c + a))) p.1.1 := by
  let G := picardGRecon ha haL e ell κ he hκ z hl hg
  let A := picardARecon ha haL e ell κ he hκ z hl hg
  let P := picardPRecon ha haL e ell κ he hκ z hl hg
  have hvalue (q : PicardDomain c a L) : z.1.1 q =
      (picardLamFiber ha haL lam0 G q.1.2 q.1.1,
        picardHFiber ha haL e h0 A P q.1.2 q.1.1) :=
    (hf q).trans ((picardCarrierUpdate_value_of_center_values ha haL e ell κ he hκ
      center z hl hg lam0 h0 hc q).symm.trans
        (picardCarrierUpdate_eq_fibers_of_center_values ha haL e ell κ he hκ
          center z hl hg lam0 h0 hc q))
  have hsection (s : ℝ) (hs : s ∈ Set.Icc c (min p.1.2 (c + a))) :
      (picardCandidateLam ha haL z s p.1.2, picardCandidateH ha haL z s p.1.2) =
        (picardLamFiber ha haL lam0 G p.1.2 s, picardHFiber ha haL e h0 A P p.1.2 s) := by
    let q : PicardDomain c a L := ⟨(s, p.1.2),
      ⟨⟨hs.1, hs.2.trans (min_le_left _ _), p.2.1.2.2⟩,
        hs.2.trans (min_le_right _ _)⟩⟩
    rw [picardCandidateLam_coe ha haL z q, picardCandidateH_coe ha haL z q]
    exact hvalue q
  have hp : p.1.1 ∈ Set.Icc c (min p.1.2 (c + a)) :=
    ⟨p.2.1.1, le_min p.2.1.2.1 p.2.2⟩
  have hdLam := picardLamFiber_hasDerivAt ha haL lam0 G p.1.2 p.1.1
  have hdh := picardHFiber_hasDerivAt ha haL e h0 A P p.1.2 p.1.1
  have hLamValue : (z.1.1 p).1 = picardLamFiber ha haL lam0 G p.1.2 p.1.1 :=
    congrArg Prod.fst (hvalue p)
  have hHValue : (z.1.1 p).2 = picardHFiber ha haL e h0 A P p.1.2 p.1.1 :=
    congrArg Prod.snd (hvalue p)
  rw [picardClamp_coe ha haL p, ← hLamValue] at hdLam
  rw [picardClamp_coe ha haL p, ← hHValue] at hdh
  exact ⟨hdLam.hasDerivWithinAt.congr (fun s hs => congrArg Prod.fst (hsection s hs))
      (congrArg Prod.fst (hsection p.1.1 hp)),
    hdh.hasDerivWithinAt.congr (fun s hs => congrArg Prod.snd (hsection s hs))
      (congrArg Prod.snd (hsection p.1.1 hp))⟩

/-- At an axis point, every actual fixed point has zero incoming derivative
within the closed incoming section. The initial outgoing datum derivative
is unrestricted. These are the later-cone endpoint compatibility conditions. -/
theorem picardFixedPoint_axis_of_integral_equations (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
    (lam0 : ℝ → ℝ) (h0 : ℝ → ℂ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam0 p.1.2, h0 p.1.2))
    (hf : ∀ p : PicardDomain c a L, z.1.1 p = picardUpdate ha haL e lam0 h0 z p.1.1 p.1.2)
    (p : PicardDomain c a L) (hp : p.1.2 = p.1.1) :
    HasDerivWithinAt (fun u => picardCandidateLam ha haL z u p.1.2) 0
      (Set.Icc c p.1.1) p.1.1 ∧
    HasDerivWithinAt (fun u => picardCandidateH ha haL z u p.1.2) 0
      (Set.Icc c p.1.1) p.1.1 := by
  obtain ⟨hG, hA, hP⟩ := picardSources_axis ha haL e ell κ he hκ z hl hg p hp
  have hcut : p.1.1 ≤ c + a := p.2.2
  simpa only [hG, hA, hP, zero_mul, Complex.ofReal_zero, mul_zero, zero_add,
    hp, min_eq_left hcut] using
      picardFixedPoint_incoming_of_integral_equations ha haL e ell κ he hκ
        center z hl hg lam0 h0 hc hf p

/-- Supporting identities for `restart-sec-independent-null-construction#later-cone-map`
on any S1 wedge, including longer cones. The carrier update is the literal
map with base `c` and prescribed cone factors. Reconstruction and the map
have their regular vertex values; the incoming fibers take the prescribed
data. Axis sources vanish, and actual fixed points have zero incoming
within derivatives there. No future axis trace or outgoing datum derivative
condition is imposed. There are no estimate constants. -/
theorem laterCone_map_identities_of_center_values (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
    (lam0 : ℝ → ℝ) (h0 : ℝ → ℂ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam0 p.1.2, h0 p.1.2)) :
    let lam := picardCandidateLam ha haL z
    let hh := picardCandidateH ha haL z
    (∀ p : PicardDomain c a L,
      (picardCarrierUpdate ha haL e ell κ he hκ center z hl hg).1.1 p =
        (Recon.picardLam e lam hh c lam0 p.1.1 p.1.2,
          Recon.picardH e lam hh c h0 p.1.1 p.1.2)) ∧
    (Recon.r lam c c = 0 ∧ Recon.phi lam hh c c = hh c c ∧
      Recon.Q e lam hh c c = 0 ∧ Recon.m e lam hh c c = 0 ∧
      Recon.mu e lam hh c c = 0 ∧ Recon.nu e lam hh c c = -lam c c ∧
      Recon.A e lam hh c c = 0) ∧
    (Recon.picardLam e lam hh c lam0 c c = lam0 c ∧
      Recon.picardH e lam hh c h0 c c = h0 c) ∧
    (∀ v, picardLamFiber ha haL lam0 (picardGRecon ha haL e ell κ he hκ z hl hg) v c = lam0 v ∧
      picardHFiber ha haL e h0 (picardARecon ha haL e ell κ he hκ z hl hg)
        (picardPRecon ha haL e ell κ he hκ z hl hg) v c = h0 v) ∧
    (∀ (p : PicardDomain c a L), p.1.2 = p.1.1 →
      (picardGRecon ha haL e ell κ he hκ z hl hg).1.1 p = 0 ∧
      (picardARecon ha haL e ell κ he hκ z hl hg).1.1 p = 0 ∧
      (picardPRecon ha haL e ell κ he hκ z hl hg).1.1 p = 0) ∧
    ((∀ p : PicardDomain c a L, z.1.1 p = picardUpdate ha haL e lam0 h0 z p.1.1 p.1.2) →
      ∀ (p : PicardDomain c a L), p.1.2 = p.1.1 →
        HasDerivWithinAt (fun u => lam u p.1.2) 0 (Icc c p.1.1) p.1.1 ∧
        HasDerivWithinAt (fun u => hh u p.1.2) 0 (Icc c p.1.1) p.1.1) := by
  refine ⟨?_, Recon.laterCone_reconstruction_vertex e _ _ c,
    Recon.laterCone_picard_vertex e _ _ c lam0 h0, ?_, ?_, ?_⟩
  · exact picardCarrierUpdate_value_of_center_values ha haL e ell κ he hκ center z hl hg lam0 h0 hc
  · intro v
    exact ⟨picardLamFiber_initial ha haL lam0 _ v, picardHFiber_initial ha haL e h0 _ _ v⟩
  · exact fun p hp => picardSources_axis ha haL e ell κ he hκ z hl hg p hp
  · exact fun hf p hp =>
      picardFixedPoint_axis_of_integral_equations ha haL e ell κ he hκ
        center z hl hg lam0 h0 hc hf p hp

/-- [node restart-sec-independent-null-construction#later-cone-map]
The exact later-cone map constructs its unique fixed point on a full short
triangle. The radius and time depend only on `B,ell,|e|`, before the cone
position, actual length and C¹ datum. The first-order bounds alone enter
E5. `laterCone_map_identities_of_center_values` explicitly links the general
S1 map, prescribed starting values, vertex and fixed-point axis identities.
The preceding fiber-ODE identities establish its regular-axis compatibility
without a prescribed future axis trace or any
condition on the initial outgoing derivative. -/
theorem later_cone_map (B ell e : ℝ) (hB : 1 ≤ B) (he : 0 < ell) :
    ∃ ρ > 0, ρ ≤ 1 / 128 ∧ ρ ≤ ell / 4 ∧ ∃ τ > 0, τ ≤ 1 ∧
          ∀ (c L : ℝ) (hL : 0 < L), L ≤ τ →
          ∀ (datum : ℝ → ℝ × ℂ) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))),
          (∀ v ∈ Icc c (c + L),
            ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B) →
          (∀ v ∈ Icc c (c + L), ell ≤ (datum v).1) →
          let center := picardConeCenterOfContDiff (a := L) datum hL hc
          ∃ F : PicardBall datum center ρ → PicardBall datum center ρ,
            (∀ z p, (F z).1.1.1 p = picardUpdate hL.le le_rfl e
              (fun v => (datum v).1) (fun v => (datum v).2) z.1 p.1.1 p.1.2) ∧
            (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
            (∃! z, F z = z) ∧
            (∀ (z : PicardBall datum center ρ) p, ell / 2 ≤ (z.1.1.1 p).1 ∧
              (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam hL.le le_rfl z.1)
                (picardCandidateH hL.le le_rfl z.1) p.1.1 p.1.2) :=
  picardShortCone_contraction B ell e hB he

end EmcsfAcExtension.Local
