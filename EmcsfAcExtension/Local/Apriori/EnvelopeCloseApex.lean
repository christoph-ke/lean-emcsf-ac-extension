module

public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Continuous characteristic budgets on growing complete triangles

The incoming envelope varies with its terminal label. An affine
parametrization of each compact section reduces its continuity to a
supremum over one fixed compact interval. The integral then varies
continuously with the apex, as used in approved internal project record (20)–(22).
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E]

/-- The real incoming envelope depends continuously on both endpoints on
a fixed compact triangle. The assertion requires only continuity of the
field and introduces no uniform size or derivative bound. -/
theorem continuousOn_inEnv_toReal_apex {T : ℝ} {f : ℝ → ℝ → E}
    (hT : 0 ≤ T) (hf : ContinuousOn (Function.uncurry f) (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => (inEnv p.2 f p.1).toReal) (triangle 0 T) := by
  let G := fun p : ℝ × ℝ => Function.uncurry f (triangleProj 0 T p)
  have cG : Continuous G := continuous_comp_triangleProj hT hf
  let H := fun p : ℝ × ℝ =>
    sSup ((fun t : ℝ => ‖G (p.1, p.1 + t * (p.2 - p.1))‖) '' Icc (0 : ℝ) 1)
  have cc : Continuous (fun z : (ℝ × ℝ) × ℝ =>
      ‖G (z.1.1, z.1.1 + z.2 * (z.1.2 - z.1.1))‖) := by
    apply (cG.comp (show Continuous (fun z : (ℝ × ℝ) × ℝ =>
      (z.1.1, z.1.1 + z.2 * (z.1.2 - z.1.1))) by fun_prop)).norm
  have cH : Continuous H := isCompact_Icc.continuous_sSup
    (K := Icc (0 : ℝ) 1)
    (f := fun (p : ℝ × ℝ) (t : ℝ) => ‖G (p.1, p.1 + t * (p.2 - p.1))‖) cc
  apply cH.continuousOn.congr
  intro p hp
  have hpath (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      p.1 + t * (p.2 - p.1) ∈ Icc p.1 p.2 := by
    have h0 := mul_nonneg ht.1 (sub_nonneg.mpr hp.2.1)
    have h1 := mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr hp.2.1)
    constructor <;> linarith only [h0, h1]
  have himage : (fun t : ℝ => ‖G (p.1, p.1 + t * (p.2 - p.1))‖) '' Icc (0 : ℝ) 1 =
      (fun v : ℝ => ‖f p.1 v‖) '' Icc p.1 p.2 := by
    apply Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      refine ⟨p.1 + t * (p.2 - p.1), hpath t ht, ?_⟩
      dsimp only [G]
      rw [triangleProj_of_mem (p := (p.1, p.1 + t * (p.2 - p.1)))
        ⟨hp.1, (hpath t ht).1, (hpath t ht).2.trans hp.2.2⟩]
      rfl
    · rintro y ⟨v, hv, rfl⟩
      rcases eq_or_lt_of_le hp.2.1 with heq | hlt
      · have hv' : v = p.1 := le_antisymm (hv.2.trans heq.ge) hv.1
        refine ⟨0, by norm_num, ?_⟩
        dsimp only [G]
        rw [zero_mul, add_zero, triangleProj_of_mem
          (p := (p.1, p.1)) ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩, hv']
        rfl
      · let t := (v - p.1) / (p.2 - p.1)
        have ht : t ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (sub_nonneg.mpr hv.1) (sub_pos.mpr hlt).le,
            (div_le_one (sub_pos.mpr hlt)).mpr (sub_le_sub_right hv.2 p.1)⟩
        refine ⟨t, ht, ?_⟩
        have he : p.1 + t * (p.2 - p.1) = v := by
          dsimp only [t]
          rw [div_mul_cancel₀ _ (sub_pos.mpr hlt).ne']
          ring
        dsimp only [G]
        rw [he, triangleProj_of_mem (p := (p.1, v)) ⟨hp.1, hv.1, hv.2.trans hp.2.2⟩]
        rfl
  have cb : ContinuousOn (fun v => f p.1 v) (Icc p.1 p.2) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hp.1, hv.1, hv.2.trans hp.2.2⟩)
  have hb := isCompact_Icc.bddAbove_image cb.norm
  have h0 : 0 ≤ sSup ((fun v => ‖f p.1 v‖) '' Icc p.1 p.2) :=
    (norm_nonneg _).trans (le_csSup hb (mem_image_of_mem _ ⟨le_rfl, hp.2.1⟩))
  have he := normEnvelope_eq_ofReal (f := fun v _ => f p.1 v) hp.2.1 hb
  change inEnv p.2 f p.1 = ENNReal.ofReal
    (sSup ((fun v => ‖f p.1 v‖) '' Icc p.1 p.2)) at he
  change (inEnv p.2 f p.1).toReal = H p
  rw [he, ENNReal.toReal_ofReal h0]
  exact (congrArg sSup himage).symm

/-- The two finite envelope integrals vary continuously with the apex of
a complete triangle. The fields are fixed on the ambient triangle; no
smallness or derivative bound is used. This includes the zero apex. -/
theorem continuous_apex_envelope_integrals {T : ℝ} {f g : ℝ → ℝ → E}
    (hT : 0 ≤ T) (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hg : ContinuousOn (Function.uncurry g) (triangle 0 T)) :
    ContinuousOn (fun s => (∫⁻ v in Icc 0 s, outEnv 0 f v).toReal) (Icc 0 T) ∧
      ContinuousOn (fun s => (∫⁻ u in Icc 0 s, inEnv s g u).toReal) (Icc 0 T) := by
  have cj : ContinuousOn (fun v => (outEnv 0 f v).toReal) (Icc 0 T) := by
    intro v hv
    exact (ENNReal.continuousAt_toReal (outEnv_ne_top_of_continuousOn hf hv)).tendsto.comp
      ((continuousOn_outEnv hf) v hv)
  have hi := cj.intervalIntegrable_of_Icc (μ := volume) hT
  have cpj : ContinuousOn (fun s => ∫ v in 0..s, (outEnv 0 f v).toReal) (Icc 0 T) := by
    have hp := intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn (fun v => (outEnv 0 f v).toReal) (uIcc 0 T) volume from by
        rw [uIcc_of_le hT]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hi)
    simpa only [uIcc_of_le hT] using hp
  have ckg := continuousOn_inEnv_toReal_apex hT hg
  have ckg' : ContinuousOn (Function.uncurry (fun u v => (inEnv v g u).toReal))
      (triangle 0 T) := ckg
  have cpk : ContinuousOn (fun s => ∫ u in 0..s, (inEnv s g u).toReal) (Icc 0 T) :=
    (continuousOn_integral_incoming (F := fun u v => (inEnv v g u).toReal) ckg').comp
      (f := fun s : ℝ => (s, s))
      (continuous_id.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hs.1, le_rfl, hs.2⟩)
  constructor
  · apply cpj.congr
    intro s hs
    change (∫⁻ v in Icc 0 s, outEnv 0 f v).toReal =
      ∫ v in 0..s, (outEnv 0 f v).toReal
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    symm
    apply integral_toReal (((continuousOn_outEnv hf).mono
      (Icc_subset_Icc le_rfl hs.2)).aemeasurable measurableSet_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact lt_top_iff_ne_top.mpr (outEnv_ne_top_of_continuousOn hf ⟨hv.1, hv.2.trans hs.2⟩)
  · apply cpk.congr
    intro s hs
    change (∫⁻ u in Icc 0 s, inEnv s g u).toReal =
      ∫ u in 0..s, (inEnv s g u).toReal
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    symm
    have hgs := hg.mono (show triangle 0 s ⊆ triangle 0 T from
      fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans hs.2⟩)
    apply integral_toReal ((continuousOn_inEnv hgs).aemeasurable measurableSet_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact lt_top_iff_ne_top.mpr (inEnv_ne_top_of_continuousOn hgs hu)

end EmcsfAcExtension.Local
