module

public import EmcsfAcExtension.Global.Interaction.IncomingOptics
public import EmcsfAcExtension.Global.Interaction.BoundaryKernels
public import EmcsfAcExtension.Global.Interaction.HistoryPairs
import EmcsfAcExtension.Local.Api.Mono
import Mathlib.Tactic

/-! # Incoming boundary optical cost summed over finite stages

Every stage includes its assigned connector. Only the given field budget
and the radius range are used, uniformly in stage count and duration.
Source: charged_SF_new_version.tex:L3754–L3756; internal project record.
-/

public section
open Set MeasureTheory
open scoped ENNReal
namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
A nonnegative integral on an ordered finite interval partition is bounded
by the sum of its closed-stage integrals. Endpoints have zero Lebesgue
measure, including the empty partition. No integrability is required. -/
theorem lintegral_finite_stages_le (N : ℕ) (a : Fin (N + 1) → ℝ) (ha : Monotone a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ u in Icc (a 0) (a (Fin.last N)), f u) ≤
      ∑ n : Fin N, ∫⁻ u in Icc (a n.castSucc) (a n.succ), f u := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun i => a i.castSucc) (fun i j hij => ha
      (Fin.castSucc_le_castSucc_iff.mpr hij))
    have h₁ : a 0 ≤ a (Fin.last N).castSucc := ha (Fin.zero_le _)
    have h₂ : a (Fin.last N).castSucc ≤ a (Fin.last (N + 1)) := ha (Fin.le_last _)
    calc
      _ = ∫⁻ u in Icc (a 0) (a (Fin.last N).castSucc) ∪
          Icc (a (Fin.last N).castSucc) (a (Fin.last (N + 1))), f u := by
        rw [Icc_union_Icc_eq_Icc h₁ h₂]
      _ ≤ (∫⁻ u in Icc (a 0) (a (Fin.last N).castSucc), f u) +
          ∫⁻ u in Icc (a (Fin.last N).castSucc) (a (Fin.last (N + 1))), f u :=
            lintegral_union_le _ _ _
      _ ≤ (∑ n : Fin N, ∫⁻ u in Icc (a n.castSucc.castSucc) (a n.succ.castSucc), f u) +
          ∫⁻ u in Icc (a (Fin.last N).castSucc) (a (Fin.last (N + 1))), f u := add_le_add hprev
            le_rfl
      _ = _ := by rw [Fin.sum_univ_castSucc]; rfl

/-- [internal]
The explicit boundary upper-mass density on any admitted stage history
has cost `2(1+(2(1-F²)-1)⁻¹) E_n/(δρ)`. The coefficient depends only on
fixed `δ,ρ,F`, uniformly in physical data, stage radius and duration. -/
theorem boundary_upper_optical_stage {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hp : 1 / 2 < 1 - F ^ 2) (n : Fin N)
    {a b v : ℝ} (hab : a ≤ b) (hbv : b ≤ v)
    (hin : inSeg a b v ⊆ exteriorDomain ui u₀ u₁ vb)
    {U : Set ℝ} (hU : MeasurableSet U) (hsub : U ⊆ Icc a b)
    (hstage : U ⊆ Icc (B.cuts n.castSucc) (B.cuts n.succ))
    (hlabel : ∀ u ∈ U, vb u ≤ v)
    (hrows : ∀ u ∈ U, outSeg u (vb u) v ⊆ exteriorDomain ui u₀ u₁ vb) :
    (∫⁻ u in U, ENNReal.ofReal
      (2 * (-S.nu u v) * S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / (2 * (1 - F ^ 2) - 1)) /
        ((1 - S.mu u v) * S.r u v ^ 2))) ≤
      ENNReal.ofReal (2 * (1 + (2 * (1 - F ^ 2) - 1)⁻¹) / (δ * ρ) * E n) := by
  let D := exteriorDomain ui u₀ u₁ vb
  let q := 2 * (1 - F ^ 2) - 1
  let β := 2 * (1 + q⁻¹) / δ
  have hq : 0 < q := by dsimp [q]; linarith only [hp]
  have hβ : 0 < β := by dsimp [β]; positivity
  have hEn := (hE n).1
  have hBn := B.radius_pos n
  have hSE : IsSolution e S D := Local.isSolution_mono hS inter_subset_left
  have hui (u : ℝ) (hu : u ∈ U) : u ∈ Icc u₀ u₁ := finite_boundary_stage_subset B n (hstage hu)
  have hpoint (u : ℝ) (hu : u ∈ U) :
      2 * (-S.nu u v) * S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / q) / ((1 - S.mu u v) * S.r u v ^ 2) ≤
      (β * E n * B.radii n) * ((-S.nu u v) / S.r u v ^ 2) := by
    have hmem : (u, v) ∈ D := hrows u hu ⟨rfl, hlabel u hu, le_rfl⟩
    have hmb : (u, vb u) ∈ D := hrows u hu ⟨rfl, le_rfl, hlabel u hu⟩
    have hr := hSE.r_pos (u, v) hmem ((B.off_axis u (hui u hu)).trans_le (hlabel u hu))
    have hrb := hS.r_pos (u, vb u) (B.mem u (hui u hu)) (B.off_axis u (hui u hu))
    have hn := neg_pos.mpr (hSE.nu_neg (u, v) hmem)
    have hgap := hδ.trans_le (hstop (u, v) hmem).2.1
    have hm : 0 ≤ S.m u (vb u) / S.r u (vb u) := by
      have heq : S.m u (vb u) / S.r u (vb u) = S.mu u (vb u) / 2 := by dsimp [Fields.mu]; ring
      rw [heq]
      exact div_nonneg (hstop (u, vb u) hmb).1 (by norm_num)
    have he := (hE n).2.1 u (hstage hu)
    have hmE : S.m u (vb u) / S.r u (vb u) ≤ E n := by
      linarith only [he, sq_nonneg ‖S.theta u (vb u) / S.lam u (vb u)‖]
    have hyE : ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 ≤ E n := by linarith only [he, hm]
    have hH0 : 0 ≤ S.m u (vb u) / S.r u (vb u) + ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / q :=
      by positivity
    have hH : S.m u (vb u) / S.r u (vb u) + ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / q ≤
        (1 + q⁻¹) * E n := by
      have hh := add_le_add hmE (div_le_div_of_nonneg_right hyE hq.le)
      exact hh.trans_eq (by ring)
    have hprod := mul_le_mul (B.radius_range n u (hstage hu)).2 hH hH0 hBn.le
    calc
      _ = ((2 * (-S.nu u v) / S.r u v ^ 2) *
          (S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
            ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / q))) / (1 - S.mu u v) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ ((2 * (-S.nu u v) / S.r u v ^ 2) * (B.radii n * ((1 + q⁻¹) * E n))) / δ := by
        apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity))
          hgap.le).trans
        exact div_le_div_of_nonneg_left (by positivity) hδ (hstop (u, v) hmem).2.1
      _ = _ := by dsimp only [β]; simp only [div_eq_mul_inv]; ring
  have hradius (u : ℝ) (hu : u ∈ U) : ρ * B.radii n ≤ S.r u v :=
    (B.radius_range n u (hstage hu)).1.trans
      ((outgoing_radius_calculus hSE (B.off_axis u (hui u hu)).le (hlabel u hu) (hrows u
        hu)).2.monotoneOn
        ⟨le_rfl, hlabel u hu⟩ ⟨hlabel u hu, le_rfl⟩ (hlabel u hu))
  calc
    _ ≤ ∫⁻ u in U, ENNReal.ofReal (β * E n * B.radii n) *
        ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2) := by
      apply setLIntegral_mono' hU
      intro u hu
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hpoint u hu)
    _ = ENNReal.ofReal (β * E n * B.radii n) *
        (∫⁻ u in U, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (β * E n * B.radii n) * ENNReal.ofReal (1 / (ρ * B.radii n)) := by
      gcongr
      exact incoming_inverse_square_kernel hSE hab hbv hin hU hsub (mul_pos hρ hBn) hradius
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [β, q]
      field_simp [hρ.ne', hBn.ne']

/-- [internal]
A nonnegative integral on any measurable portion of a finite partition
is bounded by the sum on its stage intersections. The coefficient is one
and no connectedness, integrability, or positive stage count is required. -/
theorem lintegral_finite_stages_inter_le (N : ℕ) (a : Fin (N + 1) → ℝ)
    (ha : Monotone a) {U : Set ℝ} (hU : MeasurableSet U)
    (hsub : U ⊆ Icc (a 0) (a (Fin.last N))) (f : ℝ → ℝ≥0∞) :
    (∫⁻ u in U, f u) ≤ ∑ n : Fin N, ∫⁻ u in Icc (a n.castSucc) (a n.succ) ∩ U, f u := by
  classical
  have hh := lintegral_finite_stages_le N a ha (U.indicator f)
  simp_rw [lintegral_indicator hU, Measure.restrict_restrict hU] at hh
  rw [inter_eq_left.mpr hsub] at hh
  simpa only [inter_comm] using hh

/-- [internal]
The full incoming history's explicit boundary upper-mass cost is at most
`2(1+(2(1-F²)-1)⁻¹)/(δρ)` times the sum of the actual stage budgets.
The coefficient depends only on fixed `δ,ρ,F`, uniformly in physical data,
stage number, all radii, and every stage duration. -/
theorem boundary_upper_optical_cost {e ui u₀ u₁ v₀ ρ δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (hS : IsSolution e S (origDomain ui))
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) {E : Fin N → ℝ}
    (hE : BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E)
    (hstop : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hp : 1 / 2 < 1 - F ^ 2)
    (v : ℝ) (hv : v ∈ Icc v₀ 0) :
    (∫⁻ u in {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v}, ENNReal.ofReal
      (2 * (-S.nu u v) * S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / (2 * (1 - F ^ 2) - 1)) /
        ((1 - S.mu u v) * S.r u v ^ 2))) ≤
      ENNReal.ofReal (2 * (1 + (2 * (1 - F ^ 2) - 1)⁻¹) / (δ * ρ) * ∑ n, E n) := by
  let D := exteriorDomain ui u₀ u₁ vb
  let f := fun u => ENNReal.ofReal
    (2 * (-S.nu u v) * S.r u (vb u) * (S.m u (vb u) / S.r u (vb u) +
      ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 / (2 * (1 - F ^ 2) - 1)) /
      ((1 - S.mu u v) * S.r u v ^ 2))
  let C := 2 * (1 + (2 * (1 - F ^ 2) - 1)⁻¹) / (δ * ρ)
  have hq : 0 < 2 * (1 - F ^ 2) - 1 := by linarith only [hp]
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨z, hz, hzv, hist, hin⟩ := label_history_interval B hv
  rw [hist]
  have hsub : Icc u₀ z ⊆ Icc (B.cuts 0) (B.cuts (Fin.last N)) := by
    rw [B.first, B.last]
    exact Icc_subset_Icc le_rfl hz.2
  calc
    _ ≤ ∑ n : Fin N, ∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ) ∩ Icc u₀ z, f u :=
      lintegral_finite_stages_inter_le N B.cuts B.ordered measurableSet_Icc hsub f
    _ ≤ ∑ n : Fin N, ENNReal.ofReal (C * E n) := by
      apply Finset.sum_le_sum
      intro n _
      exact boundary_upper_optical_stage hS B hE hstop hδ hρ hp n hz.1 hzv.le hin
        (measurableSet_Icc.inter measurableSet_Icc) inter_subset_right inter_subset_left
        (fun u hu => (show u ∈ {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v} from hist.symm ▸ hu.2).2)
        (fun u hu p hp => finite_boundary_row B u (finite_boundary_stage_subset B n hu.1)
          ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩)
    _ = _ := by
      symm
      change ENNReal.ofReal (C * ∑ n, E n) = _
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg hC.le (hE n).1)]

end EmcsfAcExtension.Global.InteractionEstimate
