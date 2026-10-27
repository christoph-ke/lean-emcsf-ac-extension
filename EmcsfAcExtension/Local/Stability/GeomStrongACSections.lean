module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongValueLimit

/-! # Absolute continuity in both characteristic directions

A single prescribed field limit is identified with the strong density
primitive in each orientation, so all axis endpoints are retained.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A uniform field limit with uniformly L¹-Cauchy section densities is
AC on every outgoing and incoming section. Both FTC representations
and individual density integrability are explicit analytic inputs;
there is no additional bound or estimate constant. -/
theorem stab_bicharacteristic_ac_of_strong_density_cauchy
    {T : ℝ} {F Do Di : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hIo : ∀ n u, u ∈ Icc 0 T →
      Integrable (Do n u) (volume.restrict (Icc u T)))
    (hIi : ∀ n v, v ∈ Icc 0 T →
      Integrable (fun u => Di n u v) (volume.restrict (Icc 0 v)))
    (hPo : ∀ n u, u ∈ Icc 0 T → ∀ v ∈ Icc u T,
      F n u v = F n u u + ∫ t in u..v, Do n u t)
    (hPi : ∀ n v, v ∈ Icc 0 T → ∀ u ∈ Icc 0 v,
      F n u v = F n 0 v + ∫ t in 0..u, Di n t v)
    (hCo : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ u ∈ Icc 0 T,
      (∫⁻ t in Icc u T, ‖Do n u t - Do m u t‖ₑ) < ENNReal.ofReal δ)
    (hCi : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ v ∈ Icc 0 T,
      (∫⁻ t in Icc 0 v, ‖Di n t v - Di m t v‖ₑ) < ENNReal.ofReal δ)
    (hvalue : ∀ δ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u v,
      (u, v) ∈ triangle 0 T → |F n u v - f u v| < δ) :
    (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T) ∧
      ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v := by
  let I := Icc (0 : ℝ) T
  obtain ⟨qo, hqo, hLo, hACo, hFo⟩ :=
    stab_real_ac_limit_of_uniform_and_density_cauchy
      (a := fun u : I => u.val) (b := fun _ : I => T)
      (F := fun n (u : I) t => F n u.val t) (D := fun n (u : I) t => Do n u.val t)
      (f := fun (u : I) t => f u.val t) (fun u => u.property.2)
      (fun n u => hIo n u.val u.property) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hCo δ hδ
        exact ⟨N, fun n hn m hm u => hN n hn m hm u.val u.property⟩)
      (fun n u t ht => hPo n u.val u.property t ht) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hvalue δ hδ
        exact ⟨N, fun n hn u t ht => hN n hn u.val t ⟨u.property.1, ht.1, ht.2⟩⟩)
  obtain ⟨qi, hqi, hLi, hACi, hFi⟩ :=
    stab_real_ac_limit_of_uniform_and_density_cauchy
      (a := fun _ : I => (0 : ℝ)) (b := fun v : I => v.val)
      (F := fun n (v : I) t => F n t v.val) (D := fun n (v : I) t => Di n t v.val)
      (f := fun (v : I) t => f t v.val) (fun v => v.property.1)
      (fun n v => hIi n v.val v.property) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hCi δ hδ
        exact ⟨N, fun n hn m hm v => hN n hn m hm v.val v.property⟩)
      (fun n v t ht => hPi n v.val v.property t ht) (by
        intro δ hδ
        obtain ⟨N, hN⟩ := hvalue δ hδ
        exact ⟨N, fun n hn v t ht => hN n hn t v.val ⟨ht.1, ht.2, v.property.2⟩⟩)
  exact ⟨fun u hu => hACo ⟨u, hu⟩, fun v hv => hACi ⟨v, hv⟩⟩

/-- Real AC sections have an integrable ordinary derivative and their
exact complete-section primitive, including both endpoints. This is
FTC with coefficient one and no quantitative bound assumption. -/
theorem stab_real_ac_section_primitive {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
    Integrable (deriv f) (volume.restrict (Icc a b)) ∧
      ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, deriv f t := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hf.intervalIntegrable_deriv, ?_⟩
  intro x hx
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  rw [(hf.mono hsub).integral_deriv_eq_sub]
  ring

end EmcsfAcExtension.Local
