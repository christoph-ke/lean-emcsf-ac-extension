module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Local.Apriori.SmoothSupC1Bounds
import EmcsfAcExtension.Local.Apriori.SmoothSupC1Center
import EmcsfAcExtension.Local.Apriori.SmoothSupBounds
import EmcsfAcExtension.Local.Apriori.SmoothSupUniform
import EmcsfAcExtension.Local.Apriori.SmoothSupExpansion
import EmcsfAcExtension.Local.Apriori.SmoothSupPotentialBound
import EmcsfAcExtension.Local.Apriori.SmoothSupJetBound
import EmcsfAcExtension.Local.Apriori.SmoothSupCenter
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Potential
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # A fixed-datum C¹ bound and a priori continuation parameters

The universal smallness thresholds precede the datum. The bound is then
chosen after `T,e,h` and before the already constructed complete triangle,
as in internal project record (O1–O6) and internal project record. Existence, strip extension and
complete-triangle reach remain in Construction.
-/

public section

open Set Complex
open scoped ContDiff

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#geometry-c1-bounds]
Complete geometric C¹ estimates on all existing positive complete
subtriangles of a fixed C¹ datum. Thresholds are universal. The field bound
`B`, center coefficient `C`, and coefficient-jet bound `E` are chosen after
`T,e,h` (including the datum derivative size), before the apex and solution.
The center orders retain their explicit dependence on every outgoing
derivative budget `A`. Both actual first partials of `G` are continuous
and bounded uniformly up to the axis; no second derivative is assumed. -/
theorem geometry_c1_bounds : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε₀ → chargedScale e h T ≤ δ₀ →
      ∃ B C E : ℝ, 0 < B ∧ 0 < C ∧ 0 < E ∧
        ∀ (s : ℝ) (S : Fields), 0 < s → s ≤ T →
          IsC1Solution e S (triangle 0 s) → IsRestartData S h s →
          C1BoundOn S (triangle 0 s) B ∧
          ContDiffOn ℝ 1 (Function.uncurry (smoothGeomCoeff S)) (triangle 0 s) ∧
          ContinuousOn (Function.uncurry (pdU (triangle 0 s) (smoothGeomCoeff S))) (triangle 0 s) ∧
          ContinuousOn (Function.uncurry (pdV (triangle 0 s) (smoothGeomCoeff S))) (triangle 0 s) ∧
          (∀ q ∈ triangle 0 s,
            |smoothGeomCoeff S q.1 q.2| ≤ E ∧
            |pdU (triangle 0 s) (smoothGeomCoeff S) q.1 q.2| ≤ E ∧
            |pdV (triangle 0 s) (smoothGeomCoeff S) q.1 q.2| ≤ E) ∧
          ∀ A : ℝ, 0 ≤ A →
            (∀ p ∈ triangle 0 s, ‖pdV (triangle 0 s) S.a p.1 p.2‖ ≤ A) →
            ∀ p ∈ triangle 0 s,
              ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ 4 * A * S.r p.1 p.2 ∧
              |S.Q p.1 p.2| ≤ C * A * S.r p.1 p.2 ^ 3 ∧
              S.m p.1 p.2 ≤ C * A ^ 2 * S.r p.1 p.2 ^ 3 ∧
              S.mu p.1 p.2 ≤ C * A ^ 2 * S.r p.1 p.2 ^ 2 := by
  obtain ⟨εs, δs, hεs, hδs, hscalar⟩ := scalar_c1_bounds
  obtain ⟨εu, δu, η, hεu, hδu, hη, _, hsettings⟩ :=
    smooth_uniform_settings_aux (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Cp, hCp, hpot⟩ := axis_gauge_potential_bound
  refine ⟨min εs εu, min δs δu, lt_min hεs hεu, lt_min hδs hδu, ?_⟩
  intro T e h hT hh hε hδ
  have hh1 : ContDiffOn ℝ 1 h (Icc 0 T) := hh
  obtain ⟨D, hD, hd⟩ := hscalar T e h hT hh1
    (hε.trans (min_le_left _ _)) (hδ.trans (min_le_left _ _))
  let M := 1 + ‖h 0‖ + 10 * η
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let P := Cp * |e| * M * η * T
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  obtain ⟨G, hG, hg⟩ := smooth_expansion_partials_of_bound e T M D hD.le
  obtain ⟨H, hH, ha⟩ := smooth_potential_partial_of_bound e T M D G hT hM hD.le hG.le
  let Q := 2 * |e| * M * D
  let U := 2 * (D ^ 2 + 4 * e ^ 2 * M ^ 2 * D ^ 2 * T ^ 2)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  obtain ⟨B, hB, hrecover⟩ := smooth_c1_recovery_of_bounds e T M D G H P Q U
    hT.le hM hD.le hG.le hH.le hP hQ hU
  obtain ⟨E, hE, hgeom⟩ := smooth_geom_coeff_bound_of_bounds e T M D G H P Q U
    hT.le hM hD.le hG.le hH.le hP hQ hU
  obtain ⟨C, hC, horders⟩ := smooth_center_orders_uniform_of_outgoing_bound e T M hM
  refine ⟨B, C, E, hB, hC, hE, ?_⟩
  intro s S hs hsT hS hdata
  obtain ⟨hset, _⟩ := hsettings T e h hT hh1
    (hε.trans (min_le_right _ _)) (hδ.trans (min_le_right _ _)) s S hs hsT hS hdata
  have hscalar' (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) :
      ‖pdV (triangle 0 s) S.a q.1 q.2‖ ≤ D ∧
      ‖pdU (triangle 0 s) S.b q.1 q.2 + I * e * S.A q.1 q.2 * S.b q.1 q.2‖ ≤ D ∧
      ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
      ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2 :=
    (hd s S hs hsT hS hdata q hq).2.2
  have hdecay (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) := (hscalar' q hq).2.2
  have hexp := hg s η S h hsT hset hdecay
  have hAU := ha s η S h hsT hset hdecay
    (fun q hq => ⟨(hexp q.1 q.2 hq).2.2.1, (hexp q.1 q.2 hq).1⟩)
  have hpotential (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) :
      |S.A q.1 q.2| ≤ P ∧ |pdU (triangle 0 s) S.A q.1 q.2| ≤ H := by
    refine ⟨?_, hAU q.1 q.2 hq⟩
    apply ((hpot e s η M S h hset q.1 q.2 hq).2).trans
    dsimp only [P]
    have hr : S.r q.1 q.2 ≤ T :=
      ((smooth_radius_bounds_aux hset hq).2).trans (by linarith only [hq.1, hq.2.2, hsT])
    exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hcenter (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) :
      |S.Q q.1 q.2| ≤ Q * S.r q.1 q.2 ^ 3 ∧ S.mu q.1 q.2 ≤ U * S.r q.1 q.2 ^ 2 := by
    refine ⟨smooth_charge_cubic_of_bound hset hD.le (fun q hq => (hdecay q hq).1) hq, ?_⟩
    apply ((smooth_mass_center_of_bound hset hD.le
      (fun q hq => (hdecay q hq).1) hq).2).trans
    dsimp only [U]
    gcongr
  have hc := smooth_geom_coeff_c1_aux hs hS
  exact ⟨hrecover s η S h hsT hset hscalar'
      (fun q hq => hexp q.1 q.2 hq) hpotential hcenter,
    hc, continuousOn_pdU hc (uniqueDiffOn_triangle hs),
    continuousOn_pdV hc (uniqueDiffOn_triangle hs),
    hgeom s η S h hsT hset hscalar' (fun q hq => hexp q.1 q.2 hq) hpotential hcenter,
    horders s η S h hsT hset⟩

/-- The field first-jet consequence of `geometry_c1_bounds`, with the
internal project record C¹ contract. Thresholds are universal and `B` is chosen after
`T,e,h` and before the constructed apex and solution. -/
theorem smooth_c1_bound : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
      datumVar h T ≤ ε₀ → chargedScale e h T ≤ δ₀ →
      ∃ B : ℝ, 0 < B ∧ ∀ (s : ℝ) (S : Fields), 0 < s → s ≤ T →
        IsC1Solution e S (triangle 0 s) → IsRestartData S h s →
        C1BoundOn S (triangle 0 s) B := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hmain⟩ := geometry_c1_bounds
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro T e h hT hh hε hδ
  obtain ⟨B, C, E, hB, _, _, hb⟩ := hmain T e h hT hh hε hδ
  exact ⟨B, hB, fun s S hs hsT hS hdata => (hb s S hs hsT hS hdata).1⟩

end EmcsfAcExtension.Local.Null
