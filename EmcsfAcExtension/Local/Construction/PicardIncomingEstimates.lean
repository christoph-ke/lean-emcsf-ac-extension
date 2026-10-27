module

public import EmcsfAcExtension.Local.Construction.PicardCarrierBounds
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Quantitative incoming Picard estimates

Unitary phases, real exponentials and first-jet algebra give explicit local
Lipschitz estimates. Incoming integration supplies the strip-width factor.
These are the incoming components of E3. `PicardUpdateBounds` combines them
with the complete radial coefficient bounds; the original and short-cone
constructions discharge the complete invariant-ball argument. No graph node
is closed by the conditional helpers in this module.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

private theorem picard_incoming_norm_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ha : 0 ≤ a) (haL : a ≤ L) (f : C(PicardDomain c a L, E)) :
    ‖picardIncomingComponent ha haL f‖ ≤ a * ‖f‖ := by
  have h0 : picardIncomingComponent ha haL (0 : C(PicardDomain c a L, E)) = 0 := by
    ext p
    simp [picardIncomingComponent]
  simpa only [h0, dist_zero_right] using picardIncomingComponent_dist_le ha haL f 0

private theorem picard_phase_value_dist_aux (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A B : PicardCarrier c a L ℝ) (p : PicardDomain c a L) :
    dist ((picardIncomingPhase ha haL e A).1.1 p) ((picardIncomingPhase ha haL e B).1.1 p) ≤
      |e| * a * dist A B := by
  rw [picardIncomingPhase_value, picardIncomingPhase_value]
  have hform (r : ℝ) : -(Complex.I * (e : ℂ) * (r : ℂ)) = Complex.I * ((-e * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hform, hform]
  have hp := LipschitzWith.unit_phase.dist_le_mul (-e *
    (picardIncomingComponent ha haL A.1.1 p)) (-e * (picardIncomingComponent ha haL B.1.1 p))
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul, abs_neg] at hp
  have hd : |picardIncomingComponent ha haL A.1.1 p - picardIncomingComponent ha haL B.1.1 p| ≤
      a * dist A B := by
    exact (ContinuousMap.dist_apply_le_dist p).trans
      ((picardIncomingComponent_dist_le ha haL A.1.1 B.1.1).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha))
  exact hp.trans ((mul_le_mul_of_nonneg_left hd (abs_nonneg e)).trans_eq (by ring))

/-- The phase value map gains the incoming width. Its explicit Lipschitz
constant `|e| *a` is uniform in the cone position, length, and real connections. -/
theorem picardIncomingPhase_values_dist_le (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A B : PicardCarrier c a L ℝ) :
    dist (picardIncomingPhase ha haL e A).1.1 (picardIncomingPhase ha haL e B).1.1 ≤
      |e| * a * dist A B := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  exact picard_phase_value_dist_aux ha haL e A B

/-- The outgoing phase jet is bounded by the incoming width times the
connection jet norm and `|e|`. The displayed constant is uniform in `c,L`. -/
theorem picardIncomingPhase_jets_norm_le (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) :
    ‖(picardIncomingPhase ha haL e A).1.2‖ ≤ |e| * a * picardCarrierSize A := by
  apply (ContinuousMap.norm_le _ (by positivity [picardCarrierSize_nonneg A])).mpr
  intro p
  rw [picardIncomingPhase_jet, norm_mul, picardIncomingPhase_norm, one_mul]
  simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hi : |∫ s in c..p.1.1, A.1.2 (picardClamp ha haL (s, p.1.2))| ≤
      a * picardCarrierSize A := by
    exact ((picardIncomingComponent ha haL A.1.2).norm_coe_le_norm p).trans
      ((picard_incoming_norm_aux ha haL A.1.2).trans
        (mul_le_mul_of_nonneg_left (picardCarrierSize_jets_le A) ha))
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg e)).trans_eq (by ring)

private theorem picard_phase_mul_diff_aux (x x' y y' : ℂ) :
    ‖x * y - x' * y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have heq : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

/-- The full outgoing C1 phase is locally Lipschitz with the displayed
constant depending only on `|e|,a,C`, uniformly in `c,L` and the connections.
Only the second connection's size needs the bound `C`. -/
theorem picardIncomingPhase_dist_le_of_size (ha : 0 ≤ a) (haL : a ≤ L) (e C : ℝ)
    (hC : 0 ≤ C) (A B : PicardCarrier c a L ℝ) (hB : picardCarrierSize B ≤ C) :
    dist (picardIncomingPhase ha haL e A) (picardIncomingPhase ha haL e B) ≤
      (|e| * a * (1 + |e| * a * C)) * dist A B := by
  let q : ℝ := |e| * a
  have hq : 0 ≤ q := mul_nonneg (abs_nonneg _) ha
  have hd := picardIncomingPhase_values_dist_le ha haL e A B
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · exact hd.trans (mul_le_mul_of_nonneg_right
      (by change q ≤ q * (1 + q * C); have h := mul_nonneg hq (mul_nonneg hq hC); linarith only [h])
          dist_nonneg)
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    rw [dist_eq_norm, picardIncomingPhase_jet, picardIncomingPhase_jet]
    let x := (picardIncomingPhase ha haL e A).1.1 p
    let y := (picardIncomingPhase ha haL e B).1.1 p
    let JA : ℂ := -(Complex.I * (e : ℂ)) * ((∫ s in c..p.1.1, A.1.2 (picardClamp ha haL (s, p.1.2))
        : ℝ) : ℂ)
    let JB : ℂ := -(Complex.I * (e : ℂ)) * ((∫ s in c..p.1.1, B.1.2 (picardClamp ha haL (s, p.1.2))
        : ℝ) : ℂ)
    have hx : ‖x‖ = 1 := picardIncomingPhase_norm ha haL e A p
    have hxy : ‖x - y‖ ≤ q * dist A B := by
      simpa only [dist_eq_norm] using picard_phase_value_dist_aux ha haL e A B p
    have hJB : ‖JB‖ ≤ q * C := by
      dsimp only [JB]
      simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hi := ((picardIncomingComponent ha haL B.1.2).norm_coe_le_norm p).trans
        ((picard_incoming_norm_aux ha haL B.1.2).trans
          (mul_le_mul_of_nonneg_left ((picardCarrierSize_jets_le B).trans hB) ha))
      exact (mul_le_mul_of_nonneg_left hi (abs_nonneg e)).trans_eq (by dsimp [q];ring)
    have hJ : ‖JA - JB‖ ≤ q * dist A B := by
      dsimp only [JA, JB]
      rw [←mul_sub]
      simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, ←Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      have hi : |picardIncomingComponent ha haL A.1.2 p -
        picardIncomingComponent ha haL B.1.2 p| ≤ a * dist A B :=
        (ContinuousMap.dist_apply_le_dist (f := picardIncomingComponent ha haL A.1.2)
        (g := picardIncomingComponent ha haL B.1.2) p).trans
          ((picardIncomingComponent_dist_le ha haL A.1.2 B.1.2).trans
            (mul_le_mul_of_nonneg_left (le_max_right _ _) ha))
      exact (mul_le_mul_of_nonneg_left hi (abs_nonneg e)).trans_eq (by dsimp [q];ring)
    change ‖x * JA - y * JB‖ ≤ _
    calc
      _ ≤ ‖x‖ * ‖JA - JB‖ + ‖x - y‖ * ‖JB‖ := picard_phase_mul_diff_aux x y JA JB
      _ ≤ q * dist A B + (q * dist A B) * (q * C) := by
        rw [hx, one_mul]
        exact add_le_add hJ (mul_le_mul hxy hJB (norm_nonneg _) (by positivity))
      _ = _ := by dsimp [q];ring

/-- Real exponentiation has the displayed C1 Lipschitz constant on carriers
of size at most `B`. It is uniform in geometry and uses only first jets. -/
theorem picardCarrierExp_dist_le_of_size (ha : 0 ≤ a) (haL : a ≤ L) (B : ℝ)
    (hB : 0 ≤ B) (F G : PicardCarrier c a L ℝ)
    (hF : picardCarrierSize F ≤ B) (hG : picardCarrierSize G ≤ B) :
    dist (picardCarrierExp ha haL F) (picardCarrierExp ha haL G) ≤
      (Real.exp B * (1 + B)) * dist F G := by
  have hval (H : PicardCarrier c a L ℝ) (hH : picardCarrierSize H ≤ B) (p : PicardDomain c a L) :
      |H.1.1 p| ≤ B := (H.1.1.norm_coe_le_norm p).trans ((picardCarrierSize_values_le H).trans hH)
  have hjet (H : PicardCarrier c a L ℝ) (hH : picardCarrierSize H ≤ B) (p : PicardDomain c a L) :
      |H.1.2 p| ≤ B := (H.1.2.norm_coe_le_norm p).trans ((picardCarrierSize_jets_le H).trans hH)
  have hv (p : PicardDomain c a L) : |Real.exp (F.1.1 p) - Real.exp (G.1.1 p)| ≤
      Real.exp B * dist F G := by
    have h := (LipschitzOnWith.exp_on_Iic B).dist_le_mul
      (F.1.1 p) ((le_abs_self _).trans (hval F hF p))
      (G.1.1 p) ((le_abs_self _).trans (hval G hG p))
    exact h.trans (mul_le_mul_of_nonneg_left (picardCarrier_dist_value_le F G p) (Real.exp_pos
        B).le)
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    change |Real.exp (F.1.1 p) - Real.exp (G.1.1 p)| ≤ _
    exact (hv p).trans (mul_le_mul_of_nonneg_right
      (by have h := mul_nonneg (Real.exp_pos B).le hB; linarith only [h]) dist_nonneg)
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    change |Real.exp (F.1.1 p) * F.1.2 p - Real.exp (G.1.1 p) * G.1.2 p| ≤ _
    have heq : Real.exp (F.1.1 p) * F.1.2 p - Real.exp (G.1.1 p) * G.1.2 p =
        Real.exp (F.1.1 p) * (F.1.2 p - G.1.2 p) +
          (Real.exp (F.1.1 p) - Real.exp (G.1.1 p)) * G.1.2 p := by ring
    rw [heq]
    have he : |Real.exp (F.1.1 p)| ≤ Real.exp B := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hval F hF p))
    have hj : |F.1.2 p - G.1.2 p| ≤ dist F G := picardCarrier_dist_jet_le F G p
    calc
      _ ≤ |Real.exp (F.1.1 p) * (F.1.2 p - G.1.2 p)| +
          |(Real.exp (F.1.1 p) - Real.exp (G.1.1 p)) * G.1.2 p| := abs_add_le _ _
      _ ≤ Real.exp B * dist F G + (Real.exp B * dist F G) * B := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul he hj (abs_nonneg _) (Real.exp_pos B).le)
          (mul_le_mul (hv p) (hjet G hG p) (abs_nonneg _) (by positivity))
      _ = _ := by ring

/-- Real exponentiation has the displayed C1 size bound on a size-`B` carrier,
uniformly in the geometry. -/
theorem picardCarrierExp_size_le_of_size (ha : 0 ≤ a) (haL : a ≤ L) (B : ℝ)
    (hB : 0 ≤ B) (F : PicardCarrier c a L ℝ) (hF : picardCarrierSize F ≤ B) :
    picardCarrierSize (picardCarrierExp ha haL F) ≤ Real.exp B * (1 + B) := by
  have hv (p : PicardDomain c a L) : |Real.exp (F.1.1 p)| ≤ Real.exp B := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans
      ((F.1.1.norm_coe_le_norm p).trans ((picardCarrierSize_values_le F).trans hF)))
  change max ‖_‖ ‖_‖ ≤ _
  apply max_le
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    exact (hv p).trans (by have h := mul_nonneg (Real.exp_pos B).le hB;linarith only [h])
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    change |Real.exp (F.1.1 p) * F.1.2 p| ≤ _
    rw [abs_mul]
    have hj : |F.1.2 p| ≤ B :=
      (F.1.2.norm_coe_le_norm p).trans ((picardCarrierSize_jets_le F).trans hF)
    exact (mul_le_mul (hv p) hj (abs_nonneg _) (Real.exp_pos B).le).trans
      (by have h := Real.exp_pos B;linarith only [h])

/-- The unitary phase has C1 size at most `1+|e| *a*size(A)`, uniformly in
cone position and length. Its value component has modulus exactly one. -/
theorem picardIncomingPhase_size_le (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (A : PicardCarrier c a L ℝ) :
    picardCarrierSize (picardIncomingPhase ha haL e A) ≤
      1 + |e| * a * picardCarrierSize A := by
  change max ‖_‖ ‖_‖ ≤ _
  apply max_le
  · have hv : ‖(picardIncomingPhase ha haL e A).1.1‖ ≤ 1 :=
      (ContinuousMap.norm_le _ zero_le_one).mpr (fun p => (picardIncomingPhase_norm ha haL e A
          p).le)
    have h0 : 0 ≤ |e| * a * picardCarrierSize A := by positivity [picardCarrierSize_nonneg A]
    exact hv.trans (by linarith only [h0])
  · exact (picardIncomingPhase_jets_norm_le ha haL e A).trans (by linarith)

/-- The incoming real exponential gains a factor `a` in C1 distance on
size-`B` coefficient carriers for `a ≤ 1`. Its constant depends only on `B`,
uniformly in cone position, cone length and both coefficients. -/
theorem picardIncomingExp_dist_le_of_size (ha : 0 ≤ a) (haL : a ≤ L) (ha1 : a ≤ 1)
    (B : ℝ) (hB : 0 ≤ B) (F G : PicardCarrier c a L ℝ)
    (hF : picardCarrierSize F ≤ B) (hG : picardCarrierSize G ≤ B) :
    dist (picardCarrierExp ha haL (picardIncoming ha haL F))
      (picardCarrierExp ha haL (picardIncoming ha haL G)) ≤
        a * (Real.exp B * (1 + B)) * dist F G := by
  have hb (H : PicardCarrier c a L ℝ) (hH : picardCarrierSize H ≤ B) :
      picardCarrierSize (picardIncoming ha haL H) ≤ B := by
    have h1 : a * B ≤ B := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 hB
    exact (picardCarrierSize_incoming_le ha haL H).trans
      ((mul_le_mul_of_nonneg_left hH ha).trans h1)
  calc
    _ ≤ (Real.exp B * (1 + B)) * dist (picardIncoming ha haL F) (picardIncoming ha haL G) :=
      picardCarrierExp_dist_le_of_size ha haL B hB _ _ (hb F hF) (hb G hG)
    _ ≤ (Real.exp B * (1 + B)) * (a * dist F G) :=
      mul_le_mul_of_nonneg_left ((picardIncoming_lipschitz ha haL).dist_le_mul F G) (by positivity)
    _ = _ := by ring

private theorem picard_size_sub_eq_dist_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L E) :
    picardCarrierSize (picardCarrierAdd ha haL F (picardCarrierNeg ha haL G)) = dist F G := by
  change max ‖F.1.1 + -G.1.1‖ ‖F.1.2 + -G.1.2‖ = max (dist F.1.1 G.1.1) (dist F.1.2 G.1.2)
  simp only [dist_eq_norm, sub_eq_add_neg]

/-- Real multiplication has the universal C1 product-difference bound with
numerical factor two, uniformly in geometry and all four carriers. -/
theorem picardCarrierMul_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (F F' G G' : PicardCarrier c a L ℝ) :
    dist (picardCarrierMul ha haL F G) (picardCarrierMul ha haL F' G') ≤
      2 * (picardCarrierSize F * dist G G' + dist F F' * picardCarrierSize G') := by
  have heq :
      picardCarrierAdd ha haL (picardCarrierMul ha haL F G)
          (picardCarrierNeg ha haL (picardCarrierMul ha haL F' G')) =
        picardCarrierAdd ha haL
          (picardCarrierMul ha haL F (picardCarrierAdd ha haL G (picardCarrierNeg ha haL G')))
          (picardCarrierMul ha haL (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F')) G') :=
              by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro p
    · simp only [picardCarrierAdd_value, picardCarrierNeg_value, picardCarrierMul_value]
      ring
    · simp only [picardCarrierAdd_jet, picardCarrierNeg_jet, picardCarrierMul_jet,
        picardCarrierAdd_value, picardCarrierNeg_value]
      ring
  rw [←picard_size_sub_eq_dist_aux ha haL, heq]
  calc
    _ ≤ picardCarrierSize (picardCarrierMul ha haL F
        (picardCarrierAdd ha haL G (picardCarrierNeg ha haL G'))) +
        picardCarrierSize (picardCarrierMul ha haL
          (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F')) G') :=
      picardCarrierSize_add_le ha haL _ _
    _ ≤ 2 * picardCarrierSize F * dist G G' + 2 * dist F F' * picardCarrierSize G' := by
      simpa only [picard_size_sub_eq_dist_aux] using add_le_add
        (picardCarrierSize_mul_le ha haL F (picardCarrierAdd ha haL G (picardCarrierNeg ha haL G')))
        (picardCarrierSize_mul_le ha haL (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F'))
            G')
    _ = _ := by ring

/-- Complex multiplication has the universal C1 product-difference bound with
numerical factor two, uniformly in geometry and all four carriers. -/
theorem picardCarrierCMul_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (F F' G G' : PicardCarrier c a L ℂ) :
    dist (picardCarrierCMul ha haL F G) (picardCarrierCMul ha haL F' G') ≤
      2 * (picardCarrierSize F * dist G G' + dist F F' * picardCarrierSize G') := by
  have heq :
      picardCarrierAdd ha haL (picardCarrierCMul ha haL F G)
          (picardCarrierNeg ha haL (picardCarrierCMul ha haL F' G')) =
        picardCarrierAdd ha haL
          (picardCarrierCMul ha haL F (picardCarrierAdd ha haL G (picardCarrierNeg ha haL G')))
          (picardCarrierCMul ha haL (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F')) G') :=
              by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro p
    · simp only [picardCarrierAdd_value, picardCarrierNeg_value, picardCarrierCMul_value]
      ring
    · simp only [picardCarrierAdd_jet, picardCarrierNeg_jet, picardCarrierCMul_jet,
        picardCarrierAdd_value, picardCarrierNeg_value]
      ring
  rw [←picard_size_sub_eq_dist_aux ha haL, heq]
  calc
    _ ≤ picardCarrierSize (picardCarrierCMul ha haL F
        (picardCarrierAdd ha haL G (picardCarrierNeg ha haL G'))) +
        picardCarrierSize (picardCarrierCMul ha haL
          (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F')) G') :=
      picardCarrierSize_add_le ha haL _ _
    _ ≤ 2 * picardCarrierSize F * dist G G' + 2 * dist F F' * picardCarrierSize G' := by
      simpa only [picard_size_sub_eq_dist_aux] using add_le_add
        (picardCarrierSize_cmul_le ha haL F (picardCarrierAdd ha haL G (picardCarrierNeg ha haL
            G')))
        (picardCarrierSize_cmul_le ha haL (picardCarrierAdd ha haL F (picardCarrierNeg ha haL F'))
            G')
    _ = _ := by ring

/-- Carrier addition obeys the universal sum-of-distances bound. -/
theorem picardCarrierAdd_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ha : 0 ≤ a) (haL : a ≤ L) (F F' G G' : PicardCarrier c a L E) :
    dist (picardCarrierAdd ha haL F G) (picardCarrierAdd ha haL F' G') ≤
      dist F F' + dist G G' := by
  change max (dist (F.1.1 + G.1.1) (F'.1.1 + G'.1.1))
    (dist (F.1.2 + G.1.2) (F'.1.2 + G'.1.2)) ≤ _
  apply max_le
  · exact (dist_add_add_le _ _ _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (dist_add_add_le _ _ _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- Pairing real and complex carriers has universal maximum Lipschitz bound. -/
theorem picardCarrierPair_dist_le (ha : 0 ≤ a) (haL : a ≤ L)
    (F G : PicardCarrier c a L ℝ) (H K : PicardCarrier c a L ℂ) :
    dist (picardCarrierPair ha haL F H) (picardCarrierPair ha haL G K) ≤
      max (dist F G) (dist H K) := by
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · apply (ContinuousMap.dist_le (dist_nonneg.trans (le_max_left _ _))).mpr
    intro p
    change max (dist (F.1.1 p) (G.1.1 p)) (dist (H.1.1 p) (K.1.1 p)) ≤ _
    exact max_le ((picardCarrier_dist_value_le F G p).trans (le_max_left _ _))
      ((picardCarrier_dist_value_le H K p).trans (le_max_right _ _))
  · apply (ContinuousMap.dist_le (dist_nonneg.trans (le_max_left _ _))).mpr
    intro p
    change max (dist (F.1.2 p) (G.1.2 p)) (dist (H.1.2 p) (K.1.2 p)) ≤ _
    exact max_le ((picardCarrier_dist_jet_le F G p).trans (le_max_left _ _))
      ((picardCarrier_dist_jet_le H K p).trans (le_max_right _ _))

/-- A continuous real-linear map has the same operator-norm bound on carrier
size, uniformly in the geometry and candidate. -/
theorem picardCarrierLinear_size_le {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (ha : 0 ≤ a) (haL : a ≤ L) (T : E →L[ℝ] Y) (F : PicardCarrier c a L E) :
    picardCarrierSize (picardCarrierLinear ha haL T F) ≤ ‖T‖ * picardCarrierSize F := by
  change max ‖_‖ ‖_‖ ≤ _
  apply max_le
  · apply (ContinuousMap.norm_le _ (by positivity [picardCarrierSize_nonneg F])).mpr
    intro p
    change ‖T (F.1.1 p)‖ ≤ _
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((F.1.1.norm_coe_le_norm p).trans (picardCarrierSize_values_le F)) (norm_nonneg _))
  · apply (ContinuousMap.norm_le _ (by positivity [picardCarrierSize_nonneg F])).mpr
    intro p
    change ‖T (F.1.2 p)‖ ≤ _
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((F.1.2.norm_coe_le_norm p).trans (picardCarrierSize_jets_le F)) (norm_nonneg _))

/-- The incoming Picard update is locally Lipschitz in its three coefficient
carriers, with a factor of the strip width. The positive constant depends only
on `|e|` and the common size bound `B`, uniformly in geometry, the cone center,
and all coefficient carriers. This is the incoming part of E3; radial coefficient
bounds and their candidate Lipschitz constants must still be supplied. -/
theorem picardIncomingCarrierUpdate_lipschitz_of_size (e B : ℝ) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), a ≤ 1 →
      ∀ (center : PicardCarrier c a L (ℝ × ℂ))
        (G G' A A' : PicardCarrier c a L ℝ) (P P' : PicardCarrier c a L ℂ),
      picardCarrierSize center ≤ B →
      picardCarrierSize G ≤ B → picardCarrierSize G' ≤ B →
      picardCarrierSize A ≤ B → picardCarrierSize A' ≤ B →
      picardCarrierSize P ≤ B → picardCarrierSize P' ≤ B →
      dist (picardIncomingCarrierUpdate ha haL e center G A P)
        (picardIncomingCarrierUpdate ha haL e center G' A' P') ≤
          a * K * (dist G G' + dist A A' + dist P P') := by
  let E : ℝ := |e|
  let S : ℝ := 1 + E * B
  let R : ℝ := Real.exp B * (1 + B)
  let N : ℝ := B + 2 * S * B
  have hE : 0 ≤ E := abs_nonneg e
  have hS : 0 ≤ S := by dsimp [S];positivity
  have hR : 0 ≤ R := by dsimp [R];positivity
  have hN : 0 ≤ N := by dsimp [N];positivity
  refine ⟨1 + 2 * B * R + 4 * S ^ 3 + 2 * E * S * N, by positivity, ?_⟩
  intro c a L ha haL ha1 center G G' A A' P P' hc hG hG' hA hA' hP hP'
  let Δ : ℝ := dist G G' + dist A A' + dist P P'
  have hΔ : 0 ≤ Δ := by dsimp [Δ];positivity
  have hdG : dist G G' ≤ Δ :=
      by dsimp [Δ];linarith only [(dist_nonneg : 0 ≤ dist G G'), (dist_nonneg : 0 ≤ dist A A'),
           (dist_nonneg : 0 ≤ dist P P')]
  have hdA : dist A A' ≤ Δ :=
      by dsimp [Δ];linarith only [(dist_nonneg : 0 ≤ dist G G'), (dist_nonneg : 0 ≤ dist A A'),
           (dist_nonneg : 0 ≤ dist P P')]
  have hdP : dist P P' ≤ Δ :=
      by dsimp [Δ];linarith only [(dist_nonneg : 0 ≤ dist G G'), (dist_nonneg : 0 ≤ dist A A'),
           (dist_nonneg : 0 ≤ dist P P')]
  let li := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) center
  let hi := picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) center
  have hli : picardCarrierSize li ≤ B :=
    (picardCarrierLinear_size_le ha haL _ center).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_fst_le ℝ ℝ ℂ)
        (picardCarrierSize_nonneg center)).trans (by simpa only [one_mul] using hc))
  have hhi : picardCarrierSize hi ≤ B :=
    (picardCarrierLinear_size_le ha haL _ center).trans
      ((mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ ℂ)
        (picardCarrierSize_nonneg center)).trans (by simpa only [one_mul] using hc))
  have hphase (f : ℝ) (hf : |f| = E) (C : PicardCarrier c a L ℝ) (hC : picardCarrierSize C ≤ B) :
      picardCarrierSize (picardIncomingPhase ha haL f C) ≤ S := by
    have hEa : |f| * a ≤ E := by rw [hf];simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 hE
    exact (picardIncomingPhase_size_le ha haL f C).trans (add_le_add (le_refl (1 : ℝ))
      (mul_le_mul hEa hC (picardCarrierSize_nonneg C) hE))
  have hdphase (f : ℝ) (hf : |f| = E) :
      dist (picardIncomingPhase ha haL f A) (picardIncomingPhase ha haL f A') ≤ a * (E * S) * Δ :=
          by
    have hEa : |f| * a ≤ E := by rw [hf];simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 hE
    have hS' : 1 + |f| * a * B ≤ S := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_right hEa
        hB)
    calc
      _ ≤ (|f| * a * (1 + |f| * a * B)) * dist A A' :=
        picardIncomingPhase_dist_le_of_size ha haL f B hB A A' hA'
      _ ≤ (|f| * a * S) * Δ := mul_le_mul
        (mul_le_mul_of_nonneg_left hS' (by positivity)) hdA dist_nonneg (by positivity)
      _ = _ := by rw [hf];ring
  have hdphase0 (f : ℝ) (hf : |f| = E) :
      dist (picardIncomingPhase ha haL f A) (picardIncomingPhase ha haL f A') ≤ (E * S) * Δ :=
    (hdphase f hf).trans (by
      simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right ha1 (mul_nonneg (mul_nonneg
          hE hS) hΔ))
  let psi := picardIncomingPhase ha haL e A
  let psi' := picardIncomingPhase ha haL e A'
  let ipsi := picardIncomingPhase ha haL (-e) A
  let ipsi' := picardIncomingPhase ha haL (-e) A'
  have hpsi : picardCarrierSize psi ≤ S := hphase e rfl A hA
  have hpsi' : picardCarrierSize psi' ≤ S := hphase e rfl A' hA'
  have hipsi : picardCarrierSize ipsi ≤ S := hphase (-e) (abs_neg e) A hA
  have hipsi' : picardCarrierSize ipsi' ≤ S := hphase (-e) (abs_neg e) A' hA'
  let Y := picardCarrierAdd ha haL hi (picardIncoming ha haL (picardCarrierCMul ha haL ipsi P))
  let Y' := picardCarrierAdd ha haL hi (picardIncoming ha haL (picardCarrierCMul ha haL ipsi' P'))
  have hY' : picardCarrierSize Y' ≤ N := by
    have hp : picardCarrierSize (picardCarrierCMul ha haL ipsi' P') ≤ 2 * S * B :=
      (picardCarrierSize_cmul_le ha haL _ _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left hipsi' (by norm_num)) hP'
          (picardCarrierSize_nonneg P') (by positivity))
    have hi' : picardCarrierSize (picardIncoming ha haL (picardCarrierCMul ha haL ipsi' P')) ≤ 2 * S
        * B :=
      (picardCarrierSize_incoming_le ha haL _).trans
        ((mul_le_mul_of_nonneg_left hp ha).trans (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1
              (by positivity : 0 ≤ 2 * S * B)))
    exact (picardCarrierSize_add_le ha haL _ _).trans (add_le_add hhi hi')
  have hdY : dist Y Y' ≤ a * (2 * S ^ 2) * Δ := by
    have hp : dist (picardCarrierCMul ha haL ipsi P) (picardCarrierCMul ha haL ipsi' P') ≤ 2 * S ^ 2
        * Δ := by
      calc
        _ ≤ 2 * (picardCarrierSize ipsi * dist P P' + dist ipsi ipsi' * picardCarrierSize P') :=
          picardCarrierCMul_dist_le ha haL _ _ _ _
        _ ≤ 2 * (S * Δ + ((E * S) * Δ) * B) := by
          exact mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul hipsi hdP dist_nonneg hS)
            (mul_le_mul (hdphase0 (-e) (abs_neg e)) hP' (picardCarrierSize_nonneg P')
                (by positivity))) (by norm_num)
        _ = _ := by dsimp [S];ring
    calc
      _ ≤ dist hi hi + dist (picardIncoming ha haL (picardCarrierCMul ha haL ipsi P))
          (picardIncoming ha haL (picardCarrierCMul ha haL ipsi' P')) :=
        picardCarrierAdd_dist_le ha haL _ _ _ _
      _ ≤ a * (2 * S ^ 2 * Δ) := by
        simp only [dist_self, zero_add]
        exact ((picardIncoming_lipschitz ha haL).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
            hp ha)
      _ = _ := by ring
  have hdH : dist (picardCarrierCMul ha haL psi Y) (picardCarrierCMul ha haL psi' Y') ≤
      a * (4 * S ^ 3 + 2 * E * S * N) * Δ := by
    calc
      _ ≤ 2 * (picardCarrierSize psi * dist Y Y' + dist psi psi' * picardCarrierSize Y') :=
        picardCarrierCMul_dist_le ha haL _ _ _ _
      _ ≤ 2 * (S * (a * (2 * S ^ 2) * Δ) + (a * (E * S) * Δ) * N) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul hpsi hdY dist_nonneg hS)
          (mul_le_mul (hdphase e rfl) hY' (picardCarrierSize_nonneg Y') (by positivity)))
              (by norm_num)
      _ = _ := by ring
  have hdL : dist
      (picardCarrierMul ha haL li (picardCarrierExp ha haL (picardIncoming ha haL G)))
      (picardCarrierMul ha haL li (picardCarrierExp ha haL (picardIncoming ha haL G'))) ≤ a * (2 * B
          * R) * Δ := by
    calc
      _ ≤ 2 * (picardCarrierSize li * dist (picardCarrierExp ha haL (picardIncoming ha haL G))
          (picardCarrierExp ha haL (picardIncoming ha haL G')) +
          dist li li * picardCarrierSize (picardCarrierExp ha haL (picardIncoming ha haL G'))) :=
        picardCarrierMul_dist_le ha haL _ _ _ _
      _ ≤ 2 * (B * (a * R * Δ)) := by
        simp only [dist_self, zero_mul, add_zero]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hli
          ((picardIncomingExp_dist_le_of_size ha haL ha1 B hB G G' hG hG').trans
            (mul_le_mul_of_nonneg_left hdG (by positivity))) dist_nonneg hB) (by norm_num)
      _ = _ := by ring
  change dist (picardCarrierPair ha haL _ (picardCarrierCMul ha haL psi Y))
    (picardCarrierPair ha haL _ (picardCarrierCMul ha haL psi' Y')) ≤ _
  calc
    _ ≤ max (a * (2 * B * R) * Δ) (a * (4 * S ^ 3 + 2 * E * S * N) * Δ) :=
      (picardCarrierPair_dist_le ha haL _ _ _ _).trans (max_le_max hdL hdH)
    _ ≤ a * (2 * B * R) * Δ + a * (4 * S ^ 3 + 2 * E * S * N) * Δ :=
      max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    _ ≤ _ := by have h := mul_nonneg ha hΔ;linarith only [h]

/-- With zero transport, connection and scalar source the incoming carrier
update is exactly its center, in both values and outgoing first jets. -/
theorem picardIncomingCarrierUpdate_zero (ha : 0 ≤ a) (haL : a ≤ L) (e : ℝ)
    (center : PicardCarrier c a L (ℝ × ℂ)) :
    picardIncomingCarrierUpdate ha haL e center (picardCarrierConst 0)
      (picardCarrierConst 0) (picardCarrierConst 0) = center := by
  apply Subtype.ext
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro p
  · rw [picardIncomingCarrierUpdate_value]
    simp [picardIncomingPhase_value, picardCarrierConst]
  · simp [picardIncomingCarrierUpdate, picardCarrierPair, picardIncomingPhase,
      picardCarrierAdd, picardCarrierCMul, picardCarrierMul, picardCarrierLinear,
      picardCarrierExp, picardCarrierCexp, picardIncoming, picardIncomingComponent,
      picardCarrierConst, picardCarrierOfRawDeriv]

/-- The incoming Picard update has displacement at most `a*K` from its center.
The positive constant depends only on `|e|` and the common size bound `B`,
uniformly in geometry, center and coefficients. This supplies the incoming
part of the first E3 estimate, conditional on radial coefficient bounds. -/
theorem picardIncomingCarrierUpdate_displacement_of_size (e B : ℝ) (hB : 0 ≤ B) :
    ∃ K > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), a ≤ 1 →
      ∀ (center : PicardCarrier c a L (ℝ × ℂ))
        (G A : PicardCarrier c a L ℝ) (P : PicardCarrier c a L ℂ),
      picardCarrierSize center ≤ B → picardCarrierSize G ≤ B →
      picardCarrierSize A ≤ B → picardCarrierSize P ≤ B →
      dist (picardIncomingCarrierUpdate ha haL e center G A P) center ≤ a * K := by
  obtain ⟨K, hK, hLip⟩ := picardIncomingCarrierUpdate_lipschitz_of_size e B hB
  refine ⟨1 + 3 * K * B, by positivity, ?_⟩
  intro c a L ha haL ha1 center G A P hc hG hA hP
  have hzR : picardCarrierSize (picardCarrierConst (c := c) (a := a) (L := L) (0 : ℝ)) ≤ B :=
    (picardCarrierSize_const_le 0).trans (by simpa only [norm_zero] using hB)
  have hzC : picardCarrierSize (picardCarrierConst (c := c) (a := a) (L := L) (0 : ℂ)) ≤ B :=
    (picardCarrierSize_const_le 0).trans (by simpa only [norm_zero] using hB)
  have hd := hLip c a L ha haL ha1 center G (picardCarrierConst 0)
    A (picardCarrierConst 0) P (picardCarrierConst 0) hc hG hzR hA hzR hP hzC
  rw [picardIncomingCarrierUpdate_zero] at hd
  have hs : dist G (picardCarrierConst 0) + dist A (picardCarrierConst 0) +
      dist P (picardCarrierConst 0) ≤ 3 * B := by
    rw [picardCarrier_dist_zero, picardCarrier_dist_zero, picardCarrier_dist_zero]
    linarith only [hG, hA, hP]
  exact hd.trans ((mul_le_mul_of_nonneg_left hs (mul_nonneg ha hK.le)).trans
    (by linarith only [ha]))

end EmcsfAcExtension.Local
