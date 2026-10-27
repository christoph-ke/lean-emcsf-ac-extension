module

public import EmcsfAcExtension.Local.Apriori.SmoothSupCloseK
public import EmcsfAcExtension.Local.Apriori.SmoothSupUniform
import EmcsfAcExtension.Local.Apriori.SmoothSupInitial
import EmcsfAcExtension.Local.Apriori.SmoothSupRecovery
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Scalar derivative bounds uniform in the constructed apex

Universal thresholds precede the datum. A single finite scalar bound is
then chosen after `T,e,h` and before all already existing complete
triangles, as required by internal project record (M1), (N1–N2).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#scalar-c1-bounds]
The two renormalized suprema, normalized characteristic derivatives and
linear center-decay constants have one finite bound for a fixed datum,
uniform in the complete constructed apex and solution. Universal positive
thresholds are chosen first; `B` is chosen after `T,e,h`, including the
datum's first derivative size. The ordinary connection and cross scalar
derivatives are recovered in the geometric C¹ assembly. -/
theorem Null.scalar_c1_bounds : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε₀ → chargedScale e h T ≤ δ₀ →
      ∃ B : ℝ, 0 < B ∧ ∀ (s : ℝ) (S : Fields), 0 < s → s ≤ T →
        IsC1Solution e S (triangle 0 s) → IsRestartData S h s →
        ∀ q ∈ triangle 0 s,
          ‖jC1 (triangle 0 s) S q.1 q.2‖ ≤ B ∧
          ‖kC1 e (triangle 0 s) S q.1 q.2‖ ≤ B ∧
          ‖pdV (triangle 0 s) S.a q.1 q.2‖ ≤ B ∧
          ‖pdU (triangle 0 s) S.b q.1 q.2 + I * e * S.A q.1 q.2 * S.b q.1 q.2‖ ≤ B ∧
          ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ B * S.r q.1 q.2 ∧
          ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ B * S.r q.1 q.2 := by
  obtain ⟨εj, δj, Cj, hεj, hδj, hCj, hj⟩ := j_sup_closure
  obtain ⟨εk, δk, Ck, hεk, hδk, hCk, hk⟩ := k_sup_closure
  let α := min (1 / 16) (min εj εk)
  let β := min δj δk
  have hα : 0 < α := lt_min (by norm_num) (lt_min hεj hεk)
  have hβ : 0 < β := lt_min hδj hδk
  obtain ⟨ε₀, δ₀, η, hε₀, hδ₀, hη, hηα, hsettings⟩ := smooth_uniform_settings_aux hα hβ
  have hη16 : η ≤ 1 / 16 := hηα.trans (min_le_left _ _)
  have hηj : η ≤ εj := hηα.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηk : η ≤ εk := hηα.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro T e h hT hh hε hδ
  obtain ⟨D, hD, hsize⟩ := smooth_initial_sup_size_aux hT hh
  let M := 1 + ‖h 0‖ + 10 * η
  let E := e ^ 2 * M ^ 2 * T * η
  let A := Cj * (2 * D + E)
  let K := 2 * A + Ck * E
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let B := 1 + 16 * (A + K)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by dsimp only [B]; linarith only [hA, hK]
  have hKB : K ≤ B := by dsimp only [B]; linarith only [hA, hK]
  refine ⟨B, hB, ?_⟩
  intro s S hs hsT hS hdata
  obtain ⟨hset, hscale⟩ := hsettings T e h hT hh hε hδ s S hs hsT hS hdata
  have hJ := hj e s η M S h hset hηj (hscale.trans (min_le_left _ _))
  have hI := (hsize e s η M S hs hsT hset (hη16.trans (by norm_num))).2
  have hEs : e ^ 2 * M ^ 2 * s * η ≤ E := by dsimp only [E]; gcongr
  have hJbound : (⨆ q ∈ triangle 0 s, ‖jC1 (triangle 0 s) S q.1 q.2‖ₑ) ≤
      ENNReal.ofReal A := by
    apply hJ.trans
    calc
      _ ≤ ENNReal.ofReal Cj * ENNReal.ofReal (2 * D) +
          ENNReal.ofReal (Cj * E) := by
        apply add_le_add (mul_le_mul' le_rfl hI)
        apply ENNReal.ofReal_le_ofReal
        convert mul_le_mul_of_nonneg_left hEs hCj.le using 1; ring
      _ = _ := by
        rw [← ENNReal.ofReal_mul hCj.le,
          ← ENNReal.ofReal_add (by positivity : 0 ≤ Cj * (2 * D)) (by positivity : 0 ≤ Cj * E)]
        congr 1
        dsimp only [A]
        ring
  have hKineq := hk e s η M S h hset hηk (hscale.trans (min_le_right _ _))
  have hKbound : (⨆ q ∈ triangle 0 s, ‖kC1 e (triangle 0 s) S q.1 q.2‖ₑ) ≤
      ENNReal.ofReal K := by
    apply hKineq.trans
    calc
      _ ≤ 2 * ENNReal.ofReal A + ENNReal.ofReal (Ck * E) := by
        apply add_le_add (mul_le_mul' le_rfl hJbound)
        apply ENNReal.ofReal_le_ofReal
        convert mul_le_mul_of_nonneg_left hEs hCk.le using 1; ring
      _ = _ := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * A) (by positivity : 0 ≤ Ck * E)]
  have hjpoint (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) :
      ‖jC1 (triangle 0 s) S q.1 q.2‖ ≤ A := by
    have hz := (le_iSup₂_of_le q hq le_rfl).trans hJbound
    simpa only [toReal_enorm, ENNReal.toReal_ofReal hA] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
  have hkpoint (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) :
      ‖kC1 e (triangle 0 s) S q.1 q.2‖ ≤ K := by
    have hz := (le_iSup₂_of_le q hq le_rfl).trans hKbound
    simpa only [toReal_enorm, ENNReal.toReal_ofReal hK] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
  have hr := smooth_scalar_recovery_of_bound hset hη16 hA hK hjpoint hkpoint
  intro q hq
  have hrec := hr q hq
  have hr0 := hset.radius_nonneg hq
  refine ⟨(hjpoint q hq).trans hAB, (hkpoint q hq).trans hKB,
    hrec.1.trans ?_, hrec.2.1.trans ?_, hrec.2.2.1.trans ?_, hrec.2.2.2.trans ?_⟩
  · dsimp only [B]
    linarith only [hA, hK]
  · dsimp only [B]
    linarith only [hA, hK]
  · have hz : 16 * A ≤ B := by dsimp only [B]; linarith only [hK]
    nlinarith only [mul_le_mul_of_nonneg_right hz hr0]
  · have hz : 16 * K ≤ B := by dsimp only [B]; linarith only [hA]
    nlinarith only [mul_le_mul_of_nonneg_right hz hr0]

end EmcsfAcExtension.Local
