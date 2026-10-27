module

public import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Uniform Cauchy control of the geometric and electromagnetic fields

The full classical comparison supplies these estimates on the closed triangle.
The relative radius and weighted charge estimates are converted using the
actual radius primitive and the fixed comparison box, including their axis values.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem cauchy_of_pointwise_control {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {F : ℕ → ℝ → ℝ → E} {d : ℕ → ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hd0 : ∀ n m, 0 ≤ d n m)
    (hd : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d n m < ρ)
    (hb : ∀ n m p, p ∈ triangle 0 T → ‖F n p.1 p.2 - F m p.1 p.2‖ ≤ B * d n m) :
    UniformCauchySeqOn (fun n => Function.uncurry (F n)) atTop (triangle 0 T) := by
  apply Metric.uniformCauchySeqOn_iff.2
  intro ρ hρ
  have hBp : 0 < B + 1 := by linarith only [hB]
  obtain ⟨N, hN⟩ := hd (ρ / (B + 1)) (div_pos hρ hBp)
  refine ⟨N, fun n hn m hm p hp => ?_⟩
  change dist (F n p.1 p.2) (F m p.1 p.2) < ρ
  rw [dist_eq_norm]
  calc
    ‖F n p.1 p.2 - F m p.1 p.2‖ ≤ B * d n m := hb n m p hp
    _ ≤ (B + 1) * d n m := mul_le_mul_of_nonneg_right (by linarith) (hd0 n m)
    _ < ρ := (lt_div_iff₀' hBp).1 (hN n hn m hm)

private theorem norm_le_of_supDist {E : Type*} [NormedAddCommGroup E]
    {T L : ℝ} {f g : ℝ → ℝ → E} (hL : 0 ≤ L)
    (hb : supDist T f g ≤ ENNReal.ofReal L) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    ‖f p.1 p.2 - g p.1 p.2‖ ≤ L := by
  apply (ENNReal.ofReal_le_ofReal_iff hL).1
  rw [ofReal_norm]
  exact (le_iSup₂ p hp).trans hb

private theorem geometry_pointwise_of_bounds {C e T ε M A d : ℝ}
    {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hb : StabBounds C e T M d S₁ S₂)
    {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| ≤ C * d ∧
    |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| ≤ C * d ∧
    |S₁.r p.1 p.2 - S₂.r p.1 p.2| ≤ (C * T) * d := by
  have hr₁ := stab_radius_bounds hs₁ hp.1 hp.2.1 hp.2.2
  have hr0 : 0 ≤ S₁.r p.1 p.2 :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num)).trans hr₁.1
  have hrT : S₁.r p.1 p.2 ≤ T := by linarith only [hr₁.2, hp.1, hp.2.2]
  have hg : geomDist T S₁ S₂ ≤ ENNReal.ofReal (C * d) :=
    le_add_self.trans (le_self_add.trans (le_self_add.trans (le_self_add.trans hb.main)))
  have hpt : |S₁.lam p.1 p.2 - S₂.lam p.1 p.2| +
      |S₁.nu p.1 p.2 - S₂.nu p.1 p.2| +
      |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 ≤ C * d :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC hd)).1 ((le_iSup₂ p hp).trans hg)
  have hrel0 := div_nonneg (abs_nonneg (S₁.r p.1 p.2 - S₂.r p.1 p.2)) hr0
  refine ⟨by linarith only [hpt, hrel0, abs_nonneg (S₁.nu p.1 p.2 - S₂.nu p.1 p.2)],
    by linarith only [hpt, hrel0, abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2)], ?_⟩
  rcases hp.2.1.eq_or_lt with heq | hlt
  · have hz₁ := (hs₁.c1.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).1
    have hz₂ := (hs₂.c1.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).1
    simp only [← heq, hz₁, hz₂, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hC hs₁.pos.le) hd
  · have hrel : |S₁.r p.1 p.2 - S₂.r p.1 p.2| / S₁.r p.1 p.2 ≤ C * d := by
      linarith only [hpt, abs_nonneg (S₁.lam p.1 p.2 - S₂.lam p.1 p.2),
        abs_nonneg (S₁.nu p.1 p.2 - S₂.nu p.1 p.2)]
    calc
      |S₁.r p.1 p.2 - S₂.r p.1 p.2| ≤ (C * d) * S₁.r p.1 p.2 :=
        (div_le_iff₀ (hs₁.c1.r_pos p hp hlt)).1 hrel
      _ ≤ (C * d) * T := mul_le_mul_of_nonneg_left hrT (mul_nonneg hC hd)
      _ = (C * T) * d := by ring

/-- The six directly compared real fields are uniformly Cauchy, from the
actual classical comparison input and strong data approximation. The threshold
depends only on `A`, uniformly in the triangle, coupling, sizes and sequence.
The radius conversion retains its factor `T`, the charge its factor
`|e| * M * T²`, and the potential its factor `|e| * T * M`; these factors
are used only on the fixed triangle and are not absorbed into the threshold. -/
theorem Null.geometry_uniform_cauchy_of_inputs (hstab : StabExtendedStmt)
    (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).r) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).lam) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).nu) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).mu) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).Q) atTop (triangle 0 T) ∧
        UniformCauchySeqOn (fun n => Function.uncurry (Sn n).A) atTop (triangle 0 T) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hv hlim hsmall
  have hT := (hs 0).pos
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans (hs 0).box.1
  have hd := data_dist_cauchy_of_stabSetting hs hac hv hlim
  have hd0 n m : 0 ≤ dataDist (hn n) (hn m) T :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hb n m := hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m) (hs n) (hs m) hsmall
  have hg n m p hp := geometry_pointwise_of_bounds (hs n) (hs m) hC.le (hd0 n m) (hb n m)
    (p := p) hp
  refine ⟨cauchy_of_pointwise_control (mul_nonneg hC.le hT.le) hd0 hd ?_,
    cauchy_of_pointwise_control hC.le hd0 hd ?_,
    cauchy_of_pointwise_control hC.le hd0 hd ?_,
    cauchy_of_pointwise_control hC.le hd0 hd ?_,
    cauchy_of_pointwise_control (show 0 ≤ C * |e| * M * T ^ 2 by positivity) hd0 hd ?_,
    cauchy_of_pointwise_control (show 0 ≤ C * |e| * T * M by positivity) hd0 hd ?_⟩
  · intro n m p hp
    simpa only [Real.norm_eq_abs] using (hg n m p hp).2.2
  · intro n m p hp
    simpa only [Real.norm_eq_abs] using (hg n m p hp).1
  · intro n m p hp
    simpa only [Real.norm_eq_abs] using (hg n m p hp).2.1
  · intro n m p hp
    exact norm_le_of_supDist (mul_nonneg hC.le (hd0 n m)) (hb n m).extra_mu hp
  · intro n m p hp
    have hdnm := hd0 n m
    rw [Real.norm_eq_abs]
    rcases hp.2.1.eq_or_lt with heq | hlt
    · have hz₁ := ((hs n).c1.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).2.2.1
      have hz₂ := ((hs m).c1.axis p.1 ⟨hp.1, le_rfl, heq ▸ hp.2.2⟩).2.2.1
      simp only [← heq, hz₁, hz₂, sub_self, abs_zero]
      positivity
    · have hr := stab_radius_bounds (hs n) hp.1 hp.2.1 hp.2.2
      have hr0 := ((hs n).c1.r_pos p hp hlt)
      have hrT : (Sn n).r p.1 p.2 ≤ T := by linarith only [hr.2, hp.1, hp.2.2]
      have hsq : (Sn n).r p.1 p.2 ^ 2 ≤ T ^ 2 := sq_le_sq₀ hr0.le hT.le |>.2 hrT
      calc
        |(Sn n).Q p.1 p.2 - (Sn m).Q p.1 p.2| ≤
            (C * |e| * M * dataDist (hn n) (hn m) T) * (Sn n).r p.1 p.2 ^ 2 :=
          (div_le_iff₀ (sq_pos_of_pos hr0)).1 ((hb n m).extra_Q p hp hlt)
        _ ≤ (C * |e| * M * dataDist (hn n) (hn m) T) * T ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (C * |e| * M * T ^ 2) * dataDist (hn n) (hn m) T := by ring
  · intro n m p hp
    have hdnm := hd0 n m
    have hnonneg : 0 ≤ C * |e| * T * M * dataDist (hn n) (hn m) T := by positivity
    exact norm_le_of_supDist hnonneg (hb n m).extra_A hp

end EmcsfAcExtension.Local
