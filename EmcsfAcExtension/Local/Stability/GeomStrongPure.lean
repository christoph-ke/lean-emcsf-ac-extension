module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongPureSections
import EmcsfAcExtension.Local.Stability.GeomStrongIndividualEnvelope
import EmcsfAcExtension.Local.Stability.GeomStrongEnvelopeMain
import EmcsfAcExtension.Local.Stability.W11FluxStrong
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Strong pure geometric derivative comparison

The renormalized envelope difference and quadratic flux comparison are
combined with an independently proved individual geometric budget.
This supplies the full `geomStrong` clause without assuming it.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The pure characteristic expansion derivatives have uniform L¹ pair
comparison, the classical input to the strong-convergence record at
charged_SF_new_version.tex:L5436–5439. The main Lipschitz conclusion is explicit.
Constants depend only on `A` and its uniform main constant `C₀`, before
all field, data, coupling, scale and background parameters, uniformly
in minimum radii and higher derivative bounds. -/
theorem stab_pure_geometric_derivatives_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖pdV (triangle 0 T) S₁.lam u v - pdV (triangle 0 T) S₂.lam u v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖pdU (triangle 0 T) S₁.nu u v - pdU (triangle 0 T) S₂.nu u v‖ₑ) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηe, Ce, hηe, hCe, hEnvelope⟩ :=
    stab_geometric_envelope_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηq, Cq, hηq, hCq, hFlux⟩ :=
    Stab.quadratic_flux_difference_of_main_lipschitz A C₀ hA hC₀
  let Ci := 512 * A + 3 * (4096 * A ^ 2 + 800)
  let C := 4 * Ce + 2 * Cq + 2 * C₀ * (Ci + 256 * A)
  have hCi : 0 ≤ Ci := by dsimp only [Ci]; positivity
  refine ⟨min ηe (min ηq (1 / 4)), C,
    lt_min hηe (lt_min hηq (by norm_num)), by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let G := (geomDist T S₁ S₂).toReal
  let Eo := ∫⁻ v in Icc 0 T, outEnv 0 (fun u v => geomL (triangle 0 T) S₁ u v -
    geomL (triangle 0 T) S₂ u v) v
  let Ei := ∫⁻ u in Icc 0 T, inEnv T (fun u v => geomN (triangle 0 T) S₁ u v -
    geomN (triangle 0 T) S₂ u v) u
  let Io := ∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S₂) v
  let Ii := ∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S₂) u
  let Qo := ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
    |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
      S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|
  let Qi := ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
    |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
      (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2|
  let V := ENNReal.ofReal (256 * A * ε ^ 2)
  let R := (Eo + Ei) + (Qo + Qi) + ENNReal.ofReal G * ((Io + Ii) + V)
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hσ0 : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hs := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hs, hσ0]
  have hεsq1 : ε ^ 2 ≤ 1 := by linarith only [hεsq]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hσ : sigma e M T ≤ 1 := by linarith only [hs, sq_nonneg ε]
  have hG : ENNReal.ofReal G ≤ ENNReal.ofReal B := by
    dsimp only [G]
    rw [ENNReal.ofReal_toReal (stab_geomDist_ne_top h₁s h₂s)]
    exact (le_add_of_nonneg_left bot_le).trans hmain
  have hE : Eo + Ei ≤ ENNReal.ofReal (Ce * (ε + sigma e M T) * Δ) :=
    hEnvelope T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)) hmain
  have hQ : Qo + Qi ≤ ENNReal.ofReal (Cq * Δ) :=
    hFlux T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))) hmain
  have hI : Io + Ii ≤ ENNReal.ofReal (Ci * ε ^ 2) :=
    stab_geometric_envelope_budget_c1 h₂s hA.le hεsq hσ
  have hOut : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖pdV (triangle 0 T) S₁.lam u v - pdV (triangle 0 T) S₂.lam u v‖ₑ) ≤ R := by
    apply iSup₂_le
    intro u hu
    apply (stab_pure_outgoing_section_le_c1 h₁s h₂s hεsq hu).trans
    exact add_le_add (add_le_add (le_add_of_nonneg_right bot_le)
      (le_add_of_nonneg_right bot_le)) (mul_le_mul' le_rfl
        (add_le_add (le_add_of_nonneg_right bot_le) le_rfl))
  have hIn : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖pdU (triangle 0 T) S₁.nu u v - pdU (triangle 0 T) S₂.nu u v‖ₑ) ≤ R := by
    apply iSup₂_le
    intro v hv
    apply (stab_pure_incoming_section_le_c1 h₁s h₂s hA hεsq hv).trans
    exact add_le_add (add_le_add (le_add_of_nonneg_left bot_le)
      (le_add_of_nonneg_left bot_le)) (mul_le_mul' le_rfl
        (add_le_add (le_add_of_nonneg_left bot_le) le_rfl))
  have hR : R ≤ ENNReal.ofReal (Ce * (ε + sigma e M T) * Δ) +
      ENNReal.ofReal (Cq * Δ) + ENNReal.ofReal B *
        (ENNReal.ofReal (Ci * ε ^ 2) + V) :=
    add_le_add (add_le_add hE hQ) (mul_le_mul' hG (add_le_add hI le_rfl))
  apply ((add_le_add hOut hIn).trans_eq (by ring : R + R = 2 * R)).trans
  apply (mul_le_mul' le_rfl hR).trans
  dsimp only [V]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2 * (Ce * (1 + 1) * Δ + Cq * Δ + B * (Ci * 1 + 256 * A * 1)) := by gcongr
    _ = _ := by dsimp only [C, B]; ring

end EmcsfAcExtension.Local
