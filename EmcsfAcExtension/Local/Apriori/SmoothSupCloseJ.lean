module

public import EmcsfAcExtension.Local.Apriori.SmoothSupOrdered
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourcePointwise
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Closing the outgoing renormalized supremum

The ordered curvature estimate is combined with the closed L¹ envelope
budget before absorbing the finite supremum. All thresholds precede the
datum; the resulting bound retains its initial derivative size.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem norm_le_curvature_sum (z : ℂ) :
    ‖z‖ ≤ ‖z + 2 * starRingEnd ℂ z‖ := by
  have hh := norm_sub_le (z + 2 * starRingEnd ℂ z) z
  rw [add_sub_cancel_left, norm_mul] at hh
  norm_num at hh
  linarith only [hh]

/-- The entire incoming forcing in the `j` equation has a universal
bound `C ε ‖K‖₁ ‖J‖∞ + C e² M² T ε`. The constant is independent of
the datum, apex, coupling, and all initial derivative norms. -/
theorem smooth_j_forcing_sup_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ 1 / 8 →
      ∀ v ∈ Icc 0 T,
      (∫⁻ u in Icc 0 v,
        ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
          (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ) ≤
        ENNReal.ofReal (C * ε) *
          (∫⁻ a in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) a) *
          (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
  obtain ⟨A, hA, ha⟩ := Null.ordered_sup_curvature
  obtain ⟨B, hB, hb⟩ := characteristic_forcing_scalar_majorants
  refine ⟨3 * A + B, by positivity, ?_⟩
  intro e T ε M S h hset hε v hv
  have hε0 := hset.eps_nonneg
  have hp : (1 : ℝ) / 2 ≤ 1 - 16 * ε ^ 2 := by nlinarith only [hε0, hε]
  let F := fun u => ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
    (curvScalar (triangle 0 T) S u v +
      2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))‖ₑ
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 v) :
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ ≤
        3 * F u + ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) := by
    have hpuv : (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hs := (hb e T ε M S h hset (hε.trans (by norm_num)) u v hpuv).1
    have hgeom : (-S.nu u v) * S.lam u v ≤ 1 := by
      have hbox := hset.box (u, v) hpuv
      exact (mul_le_mul hbox.2.2.2.1 hbox.2.1
        (hset.c1.lam_pos _ hpuv).le (by norm_num)).trans_eq (one_mul _)
    have hscalar := mul_le_mul_of_nonneg_left
      (norm_le_curvature_sum (curvScalar (triangle 0 T) S u v))
      (norm_nonneg (S.nu u v * S.theta u v / S.r u v ^ 2))
    rw [← norm_mul, ← norm_mul] at hscalar
    have he := mul_le_mul_of_nonneg_left hgeom
      (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
    have hs' : ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ ≤
        3 * ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
          (curvScalar (triangle 0 T) S u v +
            2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))‖ +
        B * e ^ 2 * M ^ 2 * ε := by
      nlinarith only [hs, hscalar, he]
    have hh := ENNReal.ofReal_le_ofReal hs'
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hh
    simpa only [F, ENNReal.ofReal_ofNat, ofReal_norm] using hh
  have hF := ha e T ε M S h hset (1 / 2) (by norm_num) hp v v hv.1 le_rfl hv.2
  change (∫⁻ u in Icc 0 v, F u) ≤ _ at hF
  calc
    _ ≤ ∫⁻ u in Icc 0 v, 3 * F u + ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ ≤ 3 * (∫⁻ u in Icc 0 v, F u) +
        ENNReal.ofReal (B * e ^ 2 * M ^ 2 * T * ε) := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ (by finiteness), setLIntegral_const, Real.volume_Icc,
        sub_zero]
      apply add_le_add le_rfl
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ B * e ^ 2 * M ^ 2 * ε)]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hv.2
        (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
      nlinarith only [hh]
    _ ≤ 3 * (ENNReal.ofReal (A * ε / (1 + 1 / 2)) *
          (∫⁻ a in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) a) *
          (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ)) +
        ENNReal.ofReal (B * e ^ 2 * M ^ 2 * T * ε) :=
      add_le_add (mul_le_mul' le_rfl hF) le_rfl
    _ ≤ _ := by
      have hc : (3 : ℝ≥0∞) * ENNReal.ofReal (A * ε / (1 + 1 / 2)) ≤
          ENNReal.ofReal ((3 * A + B) * ε) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        apply ENNReal.ofReal_le_ofReal
        have hh := div_le_self (mul_nonneg hA.le hε0)
          (by norm_num : (1 : ℝ) ≤ 1 + 1 / 2)
        nlinarith only [hh, mul_nonneg hB.le hε0]
      rw [← mul_assoc, ← mul_assoc]
      apply add_le_add (mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl)
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right
        (show B ≤ 3 * A + B by linarith only [hA])
        (show 0 ≤ e ^ 2 * M ^ 2 * T * ε by have := hset.pos; positivity)
      simpa only [mul_assoc] using hh

private theorem renormalized_sup_finite {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image
    (continuousOn_jC1_aux hT hS).norm
  apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup₂_le
  intro q hq
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hq))

/-- [node restart-sec-independent-null-construction#j-sup-closure]
The outgoing supremum closes under universal positive thresholds, chosen
before all data. Its bound retains the actual initial `j` supremum and
the electric error `e² M² T ε`; the coefficient is independent of the
initial derivative size and the constructed apex. -/
theorem Null.j_sup_closure : ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) ≤
        ENNReal.ofReal C * (⨆ v ∈ Icc 0 T, ‖jC1 (triangle 0 T) S 0 v‖ₑ) +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
  obtain ⟨A, hA, htransport⟩ := j_characteristic_enorm_bound
  obtain ⟨D, hD, hforcing⟩ := smooth_j_forcing_sup_aux
  obtain ⟨εb, δb, hεb, hδb, henvelopes⟩ := closed_envelopes_sharp
  let H := Real.exp 1
  have hH : 0 < H := Real.exp_pos _
  have hH1 : 1 ≤ H := Real.one_le_exp (by norm_num)
  let L := A + H * D + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  let ε₀ := min εb (min (1 / 8) (1 / (100 * L)))
  refine ⟨ε₀, δb, 2 * H * (D + 1),
    lt_min hεb (lt_min (by norm_num) (by positivity)), hδb, by positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have hε0 := hset.eps_nonneg
  have hεb' : ε ≤ εb := hε.trans (min_le_left _ _)
  have hε8 : ε ≤ 1 / 8 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεL : ε ≤ 1 / (100 * L) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLε : L * ε ≤ 1 / 100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * L)).mp hεL
    nlinarith only [hh]
  have hAε : A * ε ≤ 1 / 100 := by
    apply le_trans _ hLε
    gcongr
    dsimp only [L]
    linarith only [mul_pos hH hD]
  have hHDε : H * D * ε ≤ 1 / 100 := by
    apply le_trans _ hLε
    gcongr
    dsimp only [L]
    linarith only [hA]
  let J := ⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ
  let I₀ := ⨆ v ∈ Icc 0 T, ‖jC1 (triangle 0 T) S 0 v‖ₑ
  let K := ∫⁻ a in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) a
  have hJ : J ≠ ⊤ := renormalized_sup_finite hset.pos hset.c1
  have hIle : I₀ ≤ J := by
    apply iSup₂_le
    intro v hv
    exact le_iSup₂_of_le (0, v) ⟨le_rfl, hv.1, hv.2⟩ le_rfl
  have hI : I₀ ≠ ⊤ := ne_top_of_le_ne_top hJ hIle
  have hKbound : K ≤ ENNReal.ofReal (9 / 8 * ε) :=
    (henvelopes e T ε M S h hset hεb' hδ).2
  have hK : K ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKbound
  have hKr : K.toReal ≤ 9 / 8 * ε := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 9 / 8 * ε)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hKbound
  have hexponent : A * ε * K.toReal ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hKr (mul_nonneg hA.le hε0)
    have hh' := mul_le_mul_of_nonneg_right hAε hε0
    nlinarith only [hh, hh', hε8, hε0]
  have hfeedback : H * D * ε * K.toReal ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hKr (by positivity : 0 ≤ H * D * ε)
    have hh' := mul_le_mul_of_nonneg_right hHDε hε0
    nlinarith only [hh, hh', hε8, hε0]
  have hsup : J ≤ ENNReal.ofReal H *
      (I₀ + ENNReal.ofReal (D * ε) * K * J +
        ENNReal.ofReal (D * e ^ 2 * M ^ 2 * T * ε)) := by
    apply iSup₂_le
    intro q hq
    have ht := htransport e T ε M S h hset hε8 q.1 q.2 hq.1 hq.2.1 hq.2.2
    have hf := hforcing e T ε M S h hset hε8 q.2 ⟨hq.1.trans hq.2.1, hq.2.2⟩
    apply ht.trans
    apply mul_le_mul'
    · rw [← incoming_envelope_integral_toReal hset.pos hset.c1]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
    · have hi : ‖jC1 (triangle 0 T) S 0 q.2‖ₑ ≤ I₀ := by
        dsimp only [I₀]
        exact le_iSup₂_of_le q.2 ⟨hq.1.trans hq.2.1, hq.2.2⟩ le_rfl
      exact (add_le_add hi hf).trans_eq (add_assoc _ _ _).symm
  have hr := ENNReal.toReal_mono (show ENNReal.ofReal H *
      (I₀ + ENNReal.ofReal (D * ε) * K * J +
        ENNReal.ofReal (D * e ^ 2 * M ^ 2 * T * ε)) ≠ ⊤ by finiteness) hsup
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH.le,
    ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hI (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ D * ε),
    ENNReal.toReal_ofReal (by have := hset.pos; positivity :
      0 ≤ D * e ^ 2 * M ^ 2 * T * ε)] at hr
  have hfb := mul_le_mul_of_nonneg_right hfeedback (show 0 ≤ J.toReal from
    ENNReal.toReal_nonneg)
  have hr' : J.toReal ≤ 2 * H * (I₀.toReal + D * e ^ 2 * M ^ 2 * T * ε) := by
    nlinarith only [hr, hfb]
  have hfinal : J.toReal ≤ (2 * H * (D + 1)) * I₀.toReal +
      (2 * H * (D + 1)) * e ^ 2 * M ^ 2 * T * ε := by
    apply hr'.trans
    have hh := hset.pos
    have hI0 : 0 ≤ I₀.toReal := ENNReal.toReal_nonneg
    have he0 : 0 ≤ e ^ 2 * M ^ 2 * T * ε := by positivity
    nlinarith only [mul_nonneg (by positivity : 0 ≤ 2 * H * D) hI0,
      mul_nonneg (by positivity : 0 ≤ 2 * H) he0]
  have hh := ENNReal.ofReal_le_ofReal hfinal
  rwa [ENNReal.ofReal_toReal hJ, ENNReal.ofReal_add (by positivity :
    0 ≤ (2 * H * (D + 1)) * I₀.toReal) (by have := hset.pos; positivity :
    0 ≤ (2 * H * (D + 1)) * e ^ 2 * M ^ 2 * T * ε),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * H * (D + 1)),
    ENNReal.ofReal_toReal hI] at hh

end EmcsfAcExtension.Local
