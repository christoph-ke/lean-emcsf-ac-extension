module

public import EmcsfAcExtension.Local.Construction.PicardAlgebra
public import EmcsfAcExtension.Local.Construction.PicardContraction

/-! # Incoming carrier update and the unitary phase

The algebraic update from given coefficient carriers preserves outgoing first
jets and the initial cone values. Identification with the literal Picard map and
its invariant-ball estimates remain analytic obligations; no graph node is closed.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- A constant value carrier with zero outgoing jet. -/
@[expose] noncomputable def picardCarrierConst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E) : PicardCarrier c a L E := by
  refine ⟨(ContinuousMap.const _ k, ContinuousMap.const _ 0), ?_⟩
  intro p
  simp
/-- Pair real and complex carriers, with their outgoing product-space jet. -/
@[expose] noncomputable def picardCarrierPair (ha : 0 ≤ a) (haL : a ≤ L)
    (x : PicardCarrier c a L ℝ) (y : PicardCarrier c a L ℂ) :
    PicardCarrier c a L (ℝ × ℂ) :=
  picardCarrierOfRawDeriv
    (fun u v => (picardCarrierValue ha haL x u v, picardCarrierValue ha haL y u v))
    ⟨fun p => (x.1.1 p, y.1.1 p), x.1.1.continuous.prodMk y.1.1.continuous⟩
    ⟨fun p => (x.1.2 p, y.1.2 p), x.1.2.continuous.prodMk y.1.2.continuous⟩
    (by intro p; simp only [ContinuousMap.coe_mk, picardCarrierValue_coe])
    (by
      intro p hp ht
      exact (picardCarrierValue_hasDerivAt ha haL x p hp ht).prodMk
        (picardCarrierValue_hasDerivAt ha haL y p hp ht))
/-- The incoming unitary phase as a carrier. Its real connection source
is integrated from the initial cone before exponentiation. -/
@[expose] noncomputable def picardIncomingPhase (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) : PicardCarrier c a L ℂ :=
  picardCarrierCexp ha haL (picardCarrierLinear ha haL
    ((-(Complex.I * (e : ℂ))) • Complex.ofRealCLM) (picardIncoming ha haL A))
/-- The incoming update from coefficient carriers `G,A,P` and the cone
center. The factorized unitary formula preserves outgoing first-jet compatibility. -/
@[expose] noncomputable def picardIncomingCarrierUpdate (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (center : PicardCarrier c a L (ℝ × ℂ))
    (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) :
    PicardCarrier c a L (ℝ × ℂ) :=
  let li := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) center
  let hi := picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) center
  let psi := picardIncomingPhase ha haL e A
  let invpsi := picardIncomingPhase ha haL (-e) A
  picardCarrierPair ha haL
    (picardCarrierMul ha haL li (picardCarrierExp ha haL (picardIncoming ha haL G)))
    (picardCarrierCMul ha haL psi (picardCarrierAdd ha haL hi
      (picardIncoming ha haL (picardCarrierCMul ha haL invpsi P))))

/-- The phase carrier has the exact exponential of the incoming connection integral. -/
theorem picardIncomingPhase_value (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    (picardIncomingPhase ha haL e A).1.1 p = Complex.exp (-(Complex.I * (e : ℂ) *
      ((∫ s in c..p.1.1, A.1.1 (picardClamp ha haL (s, p.1.2)) : ℝ) : ℂ))) := by
  change Complex.exp ((-(Complex.I * (e : ℂ))) *
    ((∫ s in c..p.1.1, A.1.1 (picardClamp ha haL (s, p.1.2)) : ℝ) : ℂ)) = _
  congr 1
  ring

/-- The incoming phase has modulus one at every wedge point, for arbitrary real coupling. -/
theorem picardIncomingPhase_norm (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    ‖(picardIncomingPhase ha haL e A).1.1 p‖ = 1 := by
  rw [picardIncomingPhase_value, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The phase outgoing jet is its value times the integrated connection jet. -/
theorem picardIncomingPhase_jet (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    (picardIncomingPhase ha haL e A).1.2 p = (picardIncomingPhase ha haL e A).1.1 p *
      (-(Complex.I * (e : ℂ)) * ((∫ s in c..p.1.1, A.1.2 (picardClamp ha haL (s, p.1.2)) : ℝ) : ℂ))
          := rfl

/-- The coefficient-carrier update has the exact factorized incoming value formula. -/
theorem picardIncomingCarrierUpdate_value (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (center : PicardCarrier c a L (ℝ × ℂ))
    (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (p : PicardDomain c a L) :
    (picardIncomingCarrierUpdate ha haL e center G A P).1.1 p =
      ((center.1.1 p).1 * Real.exp (∫ s in c..p.1.1, G.1.1 (picardClamp ha haL (s, p.1.2))),
        (picardIncomingPhase ha haL e A).1.1 p * ((center.1.1 p).2 +
          ∫ s in c..p.1.1, (picardIncomingPhase ha haL (-e) A).1.1 (picardClamp ha haL (s, p.1.2)) *
            P.1.1 (picardClamp ha haL (s, p.1.2)))) := rfl

/-- The incoming update equals the cone center on the initial cone,
with no prescribed future-axis trace. -/
theorem picardIncomingCarrierUpdate_initial (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (center : PicardCarrier c a L (ℝ × ℂ))
    (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (p : PicardDomain c a L)
    (hp : p.1.1 = c) : (picardIncomingCarrierUpdate ha haL e center G A P).1.1 p = center.1.1 p :=
        by
  rw [picardIncomingCarrierUpdate_value, picardIncomingPhase_value]
  simp [hp]

/-- Every incoming coefficient-carrier update preserves prescribed initial cone
values. Its reconstruction coefficients still have to be supplied and estimated. -/
theorem picardIncomingCarrierUpdate_mem_initialSet (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    {datum : ℝ → ℝ × ℂ} {center : PicardCarrier c a L (ℝ × ℂ)}
    (hc : center ∈ picardInitialSet datum)
    (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) :
    picardIncomingCarrierUpdate ha haL e center G A P ∈ picardInitialSet datum := by
  apply (mem_picardInitialSet_iff datum _).mpr
  intro p hp
  rw [picardIncomingCarrierUpdate_initial ha haL e center G A P p hp]
  exact (mem_picardInitialSet_iff datum center).mp hc p hp

/-- The phase and inverse phase recover the exact oriented connection integral
between two incoming points with the same outgoing coordinate. -/
theorem picardIncomingPhase_mul_inverse (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) (p q : PicardDomain c a L) (hq : q.1.2 = p.1.2) :
    (picardIncomingPhase ha haL e A).1.1 p * (picardIncomingPhase ha haL (-e) A).1.1 q =
      Complex.exp (-(Complex.I * (e : ℂ) *
        ((∫ t in q.1.1..p.1.1, A.1.1 (picardClamp ha haL (t, p.1.2)) : ℝ) : ℂ))) := by
  rw [picardIncomingPhase_value, picardIncomingPhase_value, hq, ←Complex.exp_add]
  have hc : Continuous (fun t => A.1.1 (picardClamp ha haL (t, p.1.2))) :=
    A.1.1.continuous.comp ((continuous_picardClamp ha haL).comp
      (continuous_id.prodMk continuous_const))
  have hi := intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := volume) c
      p.1.1)
    (hc.intervalIntegrable (μ := volume) c q.1.1)
  rw [←hi]
  congr 1
  push_cast
  ring

/-- The factorized carrier scalar update equals the exact unitary
variation-of-constants formula E2/F1 for its given coefficient carriers. -/
theorem picardIncomingCarrierUpdate_h_value (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (center : PicardCarrier c a L (ℝ × ℂ))
    (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ) (p : PicardDomain c a L) :
    ((picardIncomingCarrierUpdate ha haL e center G A P).1.1 p).2 =
      (picardIncomingPhase ha haL e A).1.1 p * (center.1.1 p).2 +
      ∫ s in c..p.1.1, Complex.exp (-(Complex.I * (e : ℂ) *
        ((∫ t in s..p.1.1, A.1.1 (picardClamp ha haL (t, p.1.2)) : ℝ) : ℂ))) *
        P.1.1 (picardClamp ha haL (s, p.1.2)) := by
  rw [picardIncomingCarrierUpdate_value]
  dsimp only
  rw [mul_add, ←intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.1] at hs
  let q : PicardDomain c a L := ⟨(s, p.1.2),
    ⟨⟨hs.1, hs.2.trans p.2.1.2.1, p.2.1.2.2⟩, hs.2.trans p.2.2⟩⟩
  have hc : picardClamp ha haL (s, p.1.2) = q := picardClamp_coe ha haL q
  dsimp only
  rw [hc]
  calc
    _ = ((picardIncomingPhase ha haL e A).1.1 p *
        (picardIncomingPhase ha haL (-e) A).1.1 q) * P.1.1 q := by ring
    _ = _ := by rw [picardIncomingPhase_mul_inverse ha haL e A p q rfl]

end EmcsfAcExtension.Local
