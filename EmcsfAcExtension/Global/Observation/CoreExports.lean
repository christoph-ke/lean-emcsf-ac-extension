module

public import EmcsfAcExtension.Global.Observation.BoundaryExports
public import EmcsfAcExtension.Global.Observation.CoreChargeScaling
import EmcsfAcExtension.Global.Observation.CoreCharge
import EmcsfAcExtension.Local.Calculus.RelativeCharge

/-! # Core estimates in the original observation setting

Boundary control supplies every mass and scalar boundary input. Full
outgoing sections retain the original existing regular axis; all radial
integrals use the original label and its Jacobian.
Source: charged_SF_new_version.tex:L2091–2144; internal project record (R1), (C1)–(C3).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node prop:charged-observation#full-section-mass-bound]
[node prop:charged-observation#radial-scalar-energy]
[node eq:co-scalar-core]
[node eq:co-core-charge]
[node eq:co-charge-relative]
[node eq:co-positive-k]
All core estimates on every full outgoing section of the actual normalized
observation window. Boundary mass and scalar bounds are derived from failed
observation. Both scalar inequalities, the two-link energy bound, weighted
Maxwell inequality, normalized charge bound, two-link relative-charge bound
and signed optical coefficient are exported together. Core constants and
charged threshold depend only on `δ`. Boundary and failure coefficients
are chosen after `δ,T` and `δ,T,ε`, respectively. All are fixed before
physical solution data, radius, scale, background and gauge. -/
theorem core_bounds_of_failed_observation {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ccore : ℝ, 0 < Ccore ∧ ∃ ηc : ℝ, 0 < ηc ∧
    ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let L := b / s
    let f := fun t => τ₀ + s * t / 2
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    0 < b → 0 < s → s ≤ b →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖H‖) ≤ ηc →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∀ t ∈ Icc (-T * L) (T * L),
      let u := γ.U (f t)
      let v := γ.V (f t)
      (∀ x ∈ Icc u v, 0 ≤ S.m u x / s ∧ S.m u x / s ≤ 2) ∧
      (((∫ x in u..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2) / s ≤
        2 * (S.m u v / s) / δ) ∧ 2 * (S.m u v / s) / δ ≤ 4 / δ) ∧
      ∀ x ∈ Ioc u v,
        (‖S.phi u x‖ ≤ ‖S.phi u v‖ + Real.sqrt (2 * S.m u v / δ) / Real.sqrt (S.r u x) ∧
         ‖S.phi u x‖ ≤ ‖H‖ + (2 + 2 / Real.sqrt δ) / Real.sqrt (S.r u x / s)) ∧
        (S.Q u x ^ 2 ≤ e ^ 2 *
          (∫ y in u..x, S.lam u y * (1 - S.mu u y) * ‖S.theta u y / S.lam u y‖ ^ 2) *
          (∫ y in u..x, S.lam u y * S.r u y ^ 2 * ‖S.phi u y‖ ^ 2 / (1 - S.mu u y)) ∧
         (S.Q u x / s) ^ 2 ≤ Ccore * (s * e) ^ 2 * (S.m u x / s) *
          (‖H‖ ^ 2 * (S.r u x / s) ^ 3 + (S.r u x / s) ^ 2)) ∧
        (S.Q u x ^ 2 / S.r u x ^ 2 ≤ (Ccore / 2) * (s * e) ^ 2 * S.mu u x *
          (‖H‖ ^ 2 * (S.r u x / s) ^ 2 + S.r u x / s) ∧
         (Ccore / 2) * (s * e) ^ 2 * S.mu u x *
          (‖H‖ ^ 2 * (S.r u x / s) ^ 2 + S.r u x / s) ≤
            Ccore * (|e| * b * (1 + ‖H‖)) ^ 2 * S.mu u x) ∧
        (0 ≤ (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) ∧
         (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) / (1 - S.mu u x) ≤
          S.mu u x / (1 - S.mu u x)) := by
  obtain ⟨Ccore, hCcore, hcore⟩ := co_core_charge_of_physical_boundary_bound hδ
  obtain ⟨ηc, hηc, hpositive⟩ := co_positive_k_of_physical_boundary_bound hδ
  refine ⟨Ccore, hCcore, ηc, hηc, ?_⟩
  intro T hT
  obtain ⟨C, hC, hboundary⟩ := co_boundary_control_of_failed_observation hT
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hboundary⟩ := hboundary ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure t ht
  have hbnd := (hboundary ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hscale hfailure t ht).2
  let u := γ.U (τ₀ + s * t / 2)
  let v := γ.V (τ₀ + s * t / 2)
  let H := (gaugeFields e S χ).a (γ.U τ₀) (γ.V τ₀)
  have hτ := normalized_clock_mem (τ₀ := τ₀) hs ht
  obtain ⟨huv, hseg⟩ := cylinder_full_section h.solution γ hb hτ
  have hfull := cylinder_full_section_subset_triangle h.solution γ hτ
  have hg (x) (hx : x ∈ Icc u v) : δ ≤ 1 - S.mu u x := hgap (u, x) (hfull ⟨rfl, hx⟩)
  have hrb : S.r u v = b := γ.radius _ hτ
  have hm : S.m u v ≤ 2 * s := hbnd.2.1
  have hphi : ‖S.phi u v‖ ≤ ‖H‖ + 2 * s / b := hbnd.2.2
  have hmass (x) (hx : x ∈ Icc u v) : 0 ≤ S.m u x / s ∧ S.m u x / s ≤ 2 := by
    have hh := mass_bounds_on_full_section h.solution huv.le hseg hx
    exact ⟨div_nonneg hh.1 hs.le,
      (div_le_div_of_nonneg_right hh.2 hs.le).trans ((div_le_iff₀ hs).mpr hm)⟩
  refine ⟨hmass, ⟨?_, ?_⟩, ?_⟩
  · have hh := div_le_div_of_nonneg_right (radial_scalar_energy h.solution hδ huv hseg hg) hs.le
    convert hh using 1
    ring
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hmass v ⟨huv.le, le_rfl⟩).2
      (by norm_num : (0 : ℝ) ≤ 2)) hδ.le).trans_eq (by ring)
  · intro x hx
    have hxseg : outSeg u u x ⊆ origDomain ui := by
      rintro p ⟨hp, h1, h2⟩
      exact hseg ⟨hp, h1, h2.trans hx.2⟩
    have hq := hcore e s b H S (origDomain ui) h.solution hs hsb u v huv hseg hrb hg hm hphi x hx
    have hr : 0 < S.r u x := h.solution.r_pos (u, x) (hseg ⟨rfl, hx.1.le, hx.2⟩) hx.1
    have hm0 : 0 ≤ S.m u x := (mass_bounds_on_full_section h.solution huv.le hseg ⟨hx.1.le, hx.2⟩).1
    have hmu : 0 ≤ S.mu u x := by dsimp only [Fields.mu]; positivity
    have hrb' : S.r u x ≤ b := by
      rw [← hrb]
      exact radius_le_boundary h.solution hseg ⟨hx.1.le, hx.2⟩
    have hfactor := charged_radial_factor_of_physical_scale e b s (S.r u x) H
      hb.le hs.le hr.le hsb hrb'
    have hrel : S.Q u x ^ 2 / S.r u x ^ 2 ≤ (Ccore / 2) * S.mu u x *
        (e ^ 2 * (‖H‖ ^ 2 * S.r u x ^ 2 + s * S.r u x)) := by
      apply (div_le_div_of_nonneg_right hq (sq_nonneg _)).trans_eq
      dsimp only [Fields.mu]
      field_simp
    refine ⟨⟨physical_radial_scalar_bound h.solution hδ hx.1 hx.2 hseg hg,
      co_scalar_core_of_physical_boundary_bound h.solution hδ hs hsb hx.1 hx.2 hseg hrb hm hg hphi⟩,
      ⟨Local.RelCharge.maxwell_cauchy_schwarz h.solution hx.1 hxseg, ?_⟩,
      ⟨?_, ?_⟩, hpositive e s b H S (origDomain ui) h.solution hs hsb u v huv hseg hrb hg hm hphi
        hcharged x hx⟩
    · have hh := div_le_div_of_nonneg_right hq (sq_nonneg s)
      convert hh using 1
      · rw [div_pow]
      · dsimp only [u, H]
        field_simp
    · apply hrel.trans_eq
      dsimp only [u, H]
      field_simp
    · calc
        _ = (Ccore / 2) * S.mu u x *
            (e ^ 2 * (‖H‖ ^ 2 * S.r u x ^ 2 + s * S.r u x)) := by
          dsimp only [u, H]
          field_simp
        _ ≤ (Ccore / 2) * S.mu u x * (2 * (|e| * b * (1 + ‖H‖)) ^ 2) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = _ := by dsimp only [u, H]; ring

end EmcsfAcExtension.Global.Observation
