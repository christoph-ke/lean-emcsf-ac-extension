module

public import EmcsfAcExtension.Frozen.Triangle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Strong incoming L¹ limits under addition and unitary multiplication

Pure analysis for internal project record item 7.5. Bounds and convergence are uniform over
all incoming labels; null exceptional sets are not interchanged.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Addition preserves uniform incoming section L¹ convergence. The triangle
inequality has coefficient one and is uniform in every section and family. -/
theorem incoming_sum_strong_of_strong {T : ℝ}
    {Fn Gn : ℕ → ℝ → ℝ → ℂ} {f g : ℝ → ℝ → ℂ}
    (hFn : ∀ n v, v ∈ Icc 0 T → IntervalIntegrable (Fn n · v) volume 0 v)
    (hGn : ∀ n v, v ∈ Icc 0 T → IntervalIntegrable (Gn n · v) volume 0 v)
    (hf : ∀ v ∈ Icc 0 T, IntervalIntegrable (f · v) volume 0 v)
    (hg : ∀ v ∈ Icc 0 T, IntervalIntegrable (g · v) volume 0 v)
    (hFl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖Fn n u v - f u v‖) < ρ)
    (hGl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖Gn n u v - g u v‖) < ρ) :
    ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖(Fn n u v + Gn n u v) - (f u v + g u v)‖) < ρ := by
  intro ρ hρ
  obtain ⟨NF,hNF⟩ := hFl (ρ/2) (by positivity)
  obtain ⟨NG,hNG⟩ := hGl (ρ/2) (by positivity)
  refine ⟨max NF NG, fun n hn v hv => ?_⟩
  have hif := (hFn n v hv).sub (hf v hv)
  have hig := (hGn n v hv).sub (hg v hv)
  have hmono := intervalIntegral.integral_mono_on hv.1 (hif.add hig).norm
    (hif.norm.add hig.norm) (fun u _ => norm_add_le (Fn n u v - f u v) (Gn n u v - g u v))
  rw [intervalIntegral.integral_add hif.norm hig.norm] at hmono
  have hNF' := hNF n ((le_max_left _ _).trans hn) v hv
  have hNG' := hNG n ((le_max_right _ _).trans hn) v hv
  simpa only [add_sub_add_comm] using hmono.trans_lt (by linarith only [hNF', hNG'])

/-- A uniformly converging unitary multiplier preserves a strong incoming
L¹ limit when the limiting density has uniform section norm bound `L`.
The explicit error bound is the density error plus the phase error times `L`.
`L` is a supplied bound, never a new universal estimate constant. -/
theorem incoming_unitary_strong_of_strong {T L : ℝ}
    {Pn Fn : ℕ → ℝ → ℝ → ℂ} {P f : ℝ → ℝ → ℂ} (hL : 0 ≤ L)
    (hPn : ∀ n v, v ∈ Icc 0 T → ContinuousOn (Pn n · v) (Icc 0 v))
    (hP : ∀ v ∈ Icc 0 T, ContinuousOn (P · v) (Icc 0 v))
    (hFn : ∀ n v, v ∈ Icc 0 T → IntervalIntegrable (Fn n · v) volume 0 v)
    (hf : ∀ v ∈ Icc 0 T, IntervalIntegrable (f · v) volume 0 v)
    (hunit : ∀ n p, p ∈ triangle 0 T → ‖Pn n p.1 p.2‖ = 1)
    (hbound : ∀ v ∈ Icc 0 T, (∫ u in (0 : ℝ)..v, ‖f u v‖) ≤ L)
    (hPl : TendstoUniformlyOn (fun n => Function.uncurry (Pn n)) (Function.uncurry P) atTop
        (triangle 0 T))
    (hFl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖Fn n u v - f u v‖) < ρ) :
    ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖Pn n u v * Fn n u v - P u v * f u v‖) < ρ := by
  intro ρ hρ
  let δ := ρ / (2 * (L+1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨NF,hNF⟩ := hFl (ρ/2) (by positivity)
  obtain ⟨NP,hNP⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hPl) δ hδ)
  refine ⟨max NF NP, fun n hn v hv => ?_⟩
  have hpdn : ContinuousOn (Pn n · v) (uIcc 0 v) := by simpa only [uIcc_of_le hv.1] using hPn n v hv
  have hpd : ContinuousOn (P · v) (uIcc 0 v) := by simpa only [uIcc_of_le hv.1] using hP v hv
  have hi := ((hFn n v hv).continuousOn_mul hpdn).sub ((hf v hv).continuousOn_mul hpd)
  have hid := (hFn n v hv).sub (hf v hv)
  have hupper := hid.norm.add ((hf v hv).norm.const_mul δ)
  have hmono := intervalIntegral.integral_mono_on hv.1 hi.norm hupper (fun u hu => by
    have hp : (u,v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hphase : ‖Pn n u v - P u v‖ ≤ δ := by
      simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using
        (hNP n ((le_max_right _ _).trans hn) (u,v) hp).le
    have he : Pn n u v * Fn n u v - P u v * f u v =
        Pn n u v * (Fn n u v - f u v) + (Pn n u v - P u v) * f u v := by ring
    calc
      _ ≤ ‖Pn n u v * (Fn n u v - f u v)‖ + ‖(Pn n u v - P u v) * f u v‖ :=
          by rw [he]; exact norm_add_le _ _
      _ ≤ ‖Fn n u v - f u v‖ + δ * ‖f u v‖ := by
        rw [norm_mul, norm_mul, hunit n (u,v) hp, one_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hphase (norm_nonneg _)))
  rw [intervalIntegral.integral_add hid.norm ((hf v hv).norm.const_mul δ),
    intervalIntegral.integral_const_mul] at hmono
  have hsmall := hNF n ((le_max_left _ _).trans hn) v hv
  have hδL : δ * L ≤ ρ/2 := by
    have hratio : L/(L+1) ≤ 1 := (div_le_one (by positivity : 0 < L+1)).2 (by linarith)
    calc
      _ = (ρ/2) * (L/(L+1)) := by dsimp only [δ]; field_simp
      _ ≤ _ :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ ρ/2)
  have hh := mul_le_mul_of_nonneg_left (hbound v hv) hδ.le
  exact hmono.trans_lt (by linarith only [hsmall, hh, hδL])

end EmcsfAcExtension.Local
