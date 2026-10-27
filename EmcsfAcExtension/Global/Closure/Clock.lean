module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Closure.Profiles
import EmcsfAcExtension.Global.Interaction.ForcingRepresentative
import EmcsfAcExtension.Global.Interaction.PairTonelli
import EmcsfAcExtension.Global.Observation.CylinderClock
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Global.Interaction.ElectricArea
import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Closure.Stages

/-! # The clock on a mixed finite boundary

The same density `-ν_b du` is used on cylinders and connectors. On a
connector it equals the radius loss. The electromagnetic moment and area
bounds have no factor involving a prescribed cooling duration.
Source: `charged_SF_new_version.tex:L4036–L4040`, internal project record
charged-measure-comparison.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Finite connector radius losses telescope exactly. The identity is uniform
in the number of stages and uses the prescribed geometric radii. -/
theorem connector_radius_sum (ρ b₀ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1))) =
      b₀ - stageRadius ρ b₀ N := by
  induction N with
  | zero => simp [stageRadius]
  | succ N ih => rw [Finset.sum_range_succ, ih]; ring

/-- [internal]
Add the connector clocks to the internal project record prescribed-cylinder-clock
bound. The consumer identifies each connector clock with its radius loss
using `finite_boundary_connector_clock` and the prescribed endpoint radii.
The coefficients are fixed before `b₀,ε₀,σ` and every finite prefix. -/
theorem total_boundary_clock_of_estimates (H ρ χ C ε₀ b₀ : ℝ) (σ : ℕ → ℝ)
    (hρ : 0 ≤ ρ) (hb : 0 ≤ b₀)
    (hclock : ∀ N : ℕ, (∑ n ∈ Finset.range N, stageDuration H ρ b₀ χ C ε₀ σ n) ≤
      H * b₀ / (ε₀ * (1 - ρ / χ))) :
    ∀ N : ℕ,
      (∑ n ∈ Finset.range N, stageDuration H ρ b₀ χ C ε₀ σ n) +
        (∑ n ∈ Finset.range N, (stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1))) ≤
        H * b₀ / (ε₀ * (1 - ρ / χ)) + b₀ := by
  intro N
  rw [connector_radius_sum]
  have hr : 0 ≤ stageRadius ρ b₀ N := mul_nonneg (pow_nonneg hρ _) hb
  linarith only [hclock N, hr]

/-- [internal]
The clock on a constant incoming label is exactly its radius loss, including
both endpoints. The coefficient is one and independent of all scales. -/
theorem connector_clock_eq_radius_loss {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b ≤ v) (hseg : inSeg a b v ⊆ origDomain ui) :
    cylinderClock S (fun _ => v) a b = S.r a v - S.r b v := by
  have hr := (Calculus.in_integralForm hS hab hbv hseg).1
  unfold cylinderClock
  rw [intervalIntegral.integral_neg, ← hr.2]
  ring

/-- [internal]
A connector in the finite boundary has the same clock as its constant-label
parametrization. There is no junction atom. -/
theorem finite_boundary_connector_clock {ui e u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (n : Fin N) :
    cylinderClock S vb (B.cool n) (B.cuts n.succ) =
      S.r (B.cool n) (vb (B.cool n)) -
        S.r (B.cuts n.succ) (vb (B.cuts n.succ)) := by
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i := by
    exact B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ := by
    exact (B.ordered (Fin.le_last i)).trans B.last.le
  have hc : B.cool n ∈ Icc u₀ u₁ :=
    ⟨(hfirst n.castSucc).trans (B.split n).1,
      (B.split n).2.trans (hlast n.succ)⟩
  have he : B.cuts n.succ ∈ Icc u₀ u₁ := ⟨hfirst _, hlast _⟩
  have hbc := (B.split n).2
  have hcon := B.connector n (B.cuts n.succ) ⟨hbc, le_rfl⟩
  calc
    _ = cylinderClock S (fun _ => vb (B.cool n)) (B.cool n) (B.cuts n.succ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hbc] at hu
      change -S.nu u (vb u) = -S.nu u (vb (B.cool n))
      rw [B.connector n u hu]
    _ = _ := by
      rw [connector_clock_eq_radius_loss hS hbc
        ((B.off_axis _ he).le.trans_eq hcon)]
      · rw [hcon]
      · rintro ⟨u, v⟩ ⟨hu, hue, rfl⟩
        rw [← B.connector n u ⟨hu, hue⟩]
        exact B.mem u ⟨hc.1.trans hu, hue.trans he.2⟩

/-- [node sec:charged-closure#charged-measure-comparison]
The mixed boundary clock is dominated by terminal radius loss, its first
radius moment is at most `R₀²/2`, and the stopped exterior area has the same
bound. The numerical coefficient `1/2` is universal, uniformly in the
coupling, finite prefix, partial last stage, all radii and all durations.
The charge inequality is the independently proved late relative-charge
bound, restricted to this exterior; it is not an additional core stop. -/
theorem charged_measure_comparison {ui e u₀ u₁ v₀ ρ R₀ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (hcut : u₀ ≤ u₁)
    (hR : S.r u₀ 0 = R₀)
    (hcharge : ∀ p ∈ exteriorDomain ui u₀ u₁ vb,
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2) :
    (∀ u ∈ Icc u₀ u₁, -S.nu u (vb u) ≤ -S.nu u 0) ∧
      (∫⁻ u in Icc u₀ u₁,
        ENNReal.ofReal (S.r u (vb u) * (-S.nu u (vb u)))) ≤
        ENNReal.ofReal (R₀ ^ 2 / 2) ∧
      (∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) * S.lam u v)) ≤
        ENNReal.ofReal (R₀ ^ 2 / 2) := by
  have hmem (u : ℝ) (hu : u ∈ Icc u₀ u₁) := B.mem u hu
  have hrow (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      outSeg u (vb u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    dsimp only at hx
    subst x
    exact ⟨(hmem u hu).1, (hmem u hu).2.1,
      (B.off_axis u hu).le.trans hv.1, hv.2⟩
  have hq (u : ℝ) (hu : u ∈ Icc u₀ u₁) (v : ℝ) (hv : v ∈ Icc (vb u) 0) :=
    hcharge (u, v) ⟨hrow u hu ⟨rfl, hv⟩, hu.1, hu.2, hv.1⟩
  have hclock (u : ℝ) (hu : u ∈ Icc u₀ u₁) :
      -S.nu u (vb u) ≤ -S.nu u 0 := by
    have hh := Gap.nu_out_antitone_of_charge_bound hS (B.off_axis u hu)
      (hmem u hu).2.2.2 (hrow u hu) (hq u hu)
    linarith
  have hterm : inSeg u₀ u₁ 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨hu, hue, rfl⟩
    exact hrow u ⟨hu, hue⟩ ⟨rfl, (hmem u ⟨hu, hue⟩).2.2.2, le_rfl⟩
  have hRpos : 0 < R₀ := by
    rw [← hR]
    exact hS.r_pos (u₀, 0)
      (hterm ⟨le_rfl, hcut, rfl⟩) (hmem u₀ ⟨le_rfl, hcut⟩).2.1
  have hRupper (u : ℝ) (hu : u ∈ Icc u₀ u₁) : S.r u 0 ≤ R₀ := by
    rw [← hR]
    exact (InteractionEstimate.incoming_radius_calculus hS hcut
      (hmem u₁ ⟨hcut, le_rfl⟩).2.1.le hterm).2 ⟨le_rfl, hcut⟩ hu hu.1
  have hmoment := InteractionEstimate.fixed_label_radius_moment hS hcut
    (hmem u₁ ⟨hcut, le_rfl⟩).2.1.le hterm measurableSet_Icc Subset.rfl hRpos.le
    (fun u hu => ⟨(hS.r_pos (u, 0)
      (hrow u hu ⟨rfl, (hmem u hu).2.2.2, le_rfl⟩) (hmem u hu).2.1).le,
      hRupper u hu⟩)
  refine ⟨hclock, ?_, ?_⟩
  · apply le_trans _ hmoment
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    apply ENNReal.ofReal_le_ofReal
    have hr := Gap.radius_out_le hS (B.off_axis u hu).le
      (hmem u hu).2.2.2 (hrow u hu)
    have hp := hS.r_pos (u, vb u) (hmem u hu) (B.off_axis u hu)
    have hn := neg_pos.mpr (hS.nu_neg (u, 0)
      (hrow u hu ⟨rfl, (hmem u hu).2.2.2, le_rfl⟩))
    simpa only [mul_comm] using mul_le_mul hr (hclock u hu)
      (neg_pos.mpr (hS.nu_neg (u, vb u) (hmem u hu))).le
      ((hp.le).trans hr)
  · calc
      _ ≤ ∫⁻ u in Icc u₀ u₁, ENNReal.ofReal ((-S.nu u 0) * S.r u 0) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro u hu
        exact InteractionEstimate.electric_row_area hS (B.off_axis u hu)
          (hmem u hu).2.2.2 (hrow u hu) (hq u hu)
      _ ≤ _ := hmoment

/-- [internal]
The terminal radius loses at most twice the mixed boundary clock. A strict
clock-loss target fixed at entry consequently improves the radius stop.
The clock bound is obtained from the prescribed cylinder sums and exact
connector losses, before any infinite stage is assumed to exist.
All coefficients are universal. Source: `charged_SF_new_version.tex:L4079–L4083`. -/
theorem radius_stop_improvement_of_estimates {ui e u₀ u₁ v₀ ρ R₀ K : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (hcut : u₀ ≤ u₁)
    (hR : S.r u₀ 0 = R₀)
    (hratio : ∀ u ∈ Icc u₀ u₁, -S.nu u 0 ≤ 2 * (-S.nu u (vb u)))
    (hclock : cylinderClock S vb u₀ u₁ ≤ K) (hsmall : 2 * K < R₀ / 4) :
    R₀ - S.r u₁ 0 ≤ 2 * cylinderClock S vb u₀ u₁ ∧
      3 * R₀ / 4 < S.r u₁ 0 := by
  have hterm : inSeg u₀ u₁ 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨hu, hue, rfl⟩
    have hm := B.mem u ⟨hu, hue⟩
    exact ⟨hm.1, hm.2.1, hm.2.1.le, le_rfl⟩
  have ht := (Calculus.in_integralForm hS hcut
    (B.mem u₁ ⟨hcut, le_rfl⟩).2.1.le hterm).1
  have cν := (hS.cont_nu.comp (continuousOn_id.prodMk B.cont) B.mem).neg
  have hi := cν.intervalIntegrable_of_Icc (μ := volume) hcut
  have hle := intervalIntegral.integral_mono_on hcut ht.1.neg
    (hi.const_mul 2) hratio
  change (∫ u in u₀..u₁, -S.nu u 0) ≤ ∫ u in u₀..u₁, 2 * (-S.nu u (vb u)) at hle
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, ← ht.2] at hle
  change -(S.r u₁ 0 - S.r u₀ 0) ≤ 2 * cylinderClock S vb u₀ u₁ at hle
  rw [hR] at hle
  change -(S.r u₁ 0 - R₀) ≤ 2 * cylinderClock S vb u₀ u₁ at hle
  constructor
  · linarith only [hle]
  · linarith only [hle, hclock, hsmall]

/-- [internal]
The actual mixed boundary clock is the sum of its cylinder and connector
clocks, with no junction atoms. This is an identity for every finite
boundary, independent of all prescribed durations and numerical budgets. -/
theorem finite_boundary_clock_eq_sum {ui e a b v₀ ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) :
    cylinderClock S vb a b = ∑ n : Fin N,
      (cylinderClock S vb (B.cuts n.castSucc) (B.cool n) +
        cylinderClock S vb (B.cool n) (B.cuts n.succ)) := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hfirst (i : Fin (N + 1)) : a ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ b :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hc := (hS.cont_nu.comp (continuousOn_id.prodMk B.cont) B.mem).neg
  have hi : IntervalIntegrable (fun u => -S.nu u (vb u)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hint (x : ℝ) (hx : x ∈ Icc a b) :
      IntervalIntegrable (fun u => -S.nu u (vb u)) volume a x := by
    apply hi.mono_set
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc_right hx.2
  have heq (n : Fin N) :
      cylinderClock S vb (B.cuts n.castSucc) (B.cool n) +
        cylinderClock S vb (B.cool n) (B.cuts n.succ) =
      cylinderClock S vb a (B.cuts n.succ) -
        cylinderClock S vb a (B.cuts n.castSucc) := by
    have hprev := hint _ ⟨hfirst n.castSucc, hlast n.castSucc⟩
    have hnext := hint _ ⟨hfirst n.succ, hlast n.succ⟩
    have hstage := hprev.symm.trans hnext
    have h₁ := hstage.mono_set (by
      rw [uIcc_of_le (B.split n).1,
        uIcc_of_le ((B.split n).1.trans (B.split n).2)]
      exact Icc_subset_Icc_right (B.split n).2)
    have h₂ := hstage.mono_set (by
      rw [uIcc_of_le (B.split n).2,
        uIcc_of_le ((B.split n).1.trans (B.split n).2)]
      exact Icc_subset_Icc_left (B.split n).1)
    exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).trans
      (intervalIntegral.integral_interval_sub_left hnext hprev).symm
  simp_rw [heq]
  let P := fun i : Fin (N + 1) => cylinderClock S vb a (B.cuts i)
  have h₀ := Fin.sum_univ_succ P
  have hN := Fin.sum_univ_castSucc P
  have htelescope : (∑ n : Fin N, (P n.succ - P n.castSucc)) = P (Fin.last N) - P 0 := by
    rw [Finset.sum_sub_distrib]
    linarith only [h₀, hN]
  change cylinderClock S vb a b = ∑ n : Fin N, (P n.succ - P n.castSucc)
  rw [htelescope]
  simp only [P, B.last, B.first, cylinderClock, intervalIntegral.integral_same, sub_zero]

/-- [internal]
The weighted integral in a full stage budget controls its cylinder clock
integral, including when the available cylinder is only a partial stage.
The coefficient is exactly one, uniform in duration and radius. -/
theorem cylinder_clock_integral_le_budget {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (E : Fin N → ℝ)
    (hE : BoundaryBudgets S ui a b v₀ ρ vb N B E)
    (T : Fin N → ℝ) (hT : ∀ n, 0 < T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) (n : Fin N) :
    (∫ τ in 0..T n,
      (‖S.theta ((γ n).U τ) ((γ n).V τ) / (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
       ‖S.xi ((γ n).U τ) ((γ n).V τ) / (S.nu ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
       S.mu ((γ n).U τ) ((γ n).V τ) ^ 2) / B.radii n) ≤ E n := by
  let I := Icc (B.cuts n.castSucc) (B.cuts n.succ)
  have hsub : I ⊆ Icc a b := Icc_subset_Icc
    (B.first.ge.trans (B.ordered (Fin.zero_le _)))
    ((B.ordered (Fin.le_last _)).trans B.last.le)
  have hp (u : ℝ) (hu : u ∈ I) := B.mem u (hsub hu)
  have cr := h.solution.cont_r.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have cm := h.solution.cont_m.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have cn := h.solution.cont_nu.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have cl := h.solution.cont_lam.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have ct := h.solution.cont_theta.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have cx := h.solution.cont_xi.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hp
  have hr (u : ℝ) (hu : u ∈ I) := h.solution.r_pos _ (hp u hu) (B.off_axis u (hsub hu))
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (hp u hu)).ne')
  have cz := cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (hp u hu)).ne)
  have cμ : ContinuousOn (fun u => S.mu u (vb u)) I :=
    (continuousOn_const.mul cm).div cr (fun u hu => (hr u hu).ne')
  let f := fun u => (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
    ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) / S.r u (vb u)
  have cf : ContinuousOn f I :=
    (((cy.norm.pow 2).add (cz.norm.pow 2)).add (cμ.pow 2)).div cr (fun u hu => (hr u hu).ne')
  have hcsub : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ I := by
    rw [(hends n).1, (hends n).2]
    exact Icc_subset_Icc le_rfl (B.split n).2
  have hchange := integral_clock_pullback h.solution (hT n) (γ n) vb f
    (B.cont.mono (hcsub.trans hsub)) (fun u hu => B.mem u (hsub (hcsub hu)))
    (hgraph n) (cf.mono hcsub)
  have heq : (∫ τ in 0..T n, f ((γ n).U τ)) =
      ∫ τ in 0..T n,
        (‖S.theta ((γ n).U τ) ((γ n).V τ) / (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
         ‖S.xi ((γ n).U τ) ((γ n).V τ) / (S.nu ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
         S.mu ((γ n).U τ) ((γ n).V τ) ^ 2) / B.radii n := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    have hm : τ ∈ Icc 0 (T n) := by simpa only [uIcc_of_le (hT n).le] using hτ
    dsimp only [f]
    rw [hgraph n τ hm, (γ n).radius τ hm]
  rw [← heq, ← hchange, (hends n).1, (hends n).2]
  have ci := (cf.mul cn.neg).intervalIntegrable_of_Icc
    (B.ordered (Fin.castSucc_le_succ n)) (μ := volume)
  have hn : ∀ᵐ u ∂volume.restrict (Ioc (B.cuts n.castSucc) (B.cuts n.succ)),
      0 ≤ f u * (-S.nu u (vb u)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u hu
    have hu' : u ∈ I := ⟨hu.1.le, hu.2⟩
    exact mul_nonneg (div_nonneg (by positivity) (hr u hu').le)
      (neg_pos.mpr (h.solution.nu_neg _ (hp u hu'))).le
  have hmono := intervalIntegral.integral_mono_interval le_rfl
    (B.split n).1 (B.split n).2 hn ci
  apply hmono.trans
  convert (hE n).2.2 using 1
  congr 1
  funext u
  dsimp only [f]
  ring

/-- [internal]
The actual accumulated cylinder variation satisfies the second stopped
inequality. Its density is the constructed finite incoming envelope; the
scalar background is the same canonical one used in the source estimate.
The coefficient depends only on `δ,F`, before all fields, lower expansion
bounds, stopping budgets, radii, stages and durations. The independent core
gap is supplied by late geometry, rather than an exterior bootstrap.
Source: charged_SF_new_version.tex:L4034–L4040. -/
theorem stopped_forcing_inequality_of_budgets (δ F : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hF : 0 ≤ F) (hF1 : F < 1) :
    ∃ C > 0, ∀ (ui e a b v₀ ρ R₀ c Λ ε Jstop : ℝ) (S : Fields)
      (vb : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui a b v₀ ρ vb N)
      (E T : Fin N → ℝ),
      OriginalData ui e S → ExteriorBox δ c Λ F ε ρ → 0 ≤ Jstop →
      ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε →
      S.r a 0 = R₀ → (∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      BoundaryBudgets S ui a b v₀ ρ vb N B E → (∀ n, E n ≤ F ^ 2) →
      (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) ≤
        c⁻¹ * (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal +
        C * (∑ n, E n) +
        C * Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀) := by
  obtain ⟨C, hC, hforcing⟩ := ct_forcing_of_raw_envelope δ F hδ hδ1 hF hF1
  refine ⟨C, hC, ?_⟩
  intro ui e a b v₀ ρ R₀ c Λ ε Jstop S vb N B E T h hbox hJstop hstop hR₀ hR
    hJ hcore hE hEF hT γ hends hgraph
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  obtain ⟨_, hg, hg0, hmajor, hint, _⟩ := incoming_envelope h B
  have hcurve (n : Fin N) (τ : ℝ) (hτ : τ ∈ Icc 0 (T n)) :
      (γ n).U τ ∈ Icc a b ∧ (γ n).V τ = vb ((γ n).U τ) := by
    have hm := ((γ n).strictMonoOn_U h.solution).monotoneOn
    have hl := hm (left_mem_Icc.mpr (hT n).le) hτ hτ.1
    have hr := hm hτ (right_mem_Icc.mpr (hT n).le) hτ.2
    rw [(hends n).1] at hl
    rw [(hends n).2] at hr
    exact ⟨⟨(B.first.ge.trans (B.ordered (Fin.zero_le _))).trans hl,
      hr.trans ((B.split n).2.trans ((B.ordered (Fin.le_last _)).trans B.last.le))⟩,
      (hgraph n τ hτ).symm⟩
  have horder {n m : Fin N} (hnm : n < m) : (γ n).U (T n) ≤ (γ m).U 0 := by
    rw [(hends n).2, (hends m).1]
    apply (B.split n).2.trans
    apply B.ordered
    change n.val + 1 ≤ m.val
    exact Nat.succ_le_of_lt hnm
  have hdisjU : Pairwise fun n m => Disjoint (Ioc ((γ n).U 0) ((γ n).U (T n)))
      (Ioc ((γ m).U 0) ((γ m).U (T m))) := by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with hnm | hmn
    · exact Ioc_disjoint_Ioc_of_le (horder hnm)
    · exact (Ioc_disjoint_Ioc_of_le (horder hmn)).symm
  have hdisjV : Pairwise fun n m => Disjoint (Ioc ((γ n).V 0) ((γ n).V (T n)))
      (Ioc ((γ m).V 0) ((γ m).V (T m))) := by
    intro n m hnm
    have ho {n m : Fin N} (hnm : n < m) : (γ n).V (T n) ≤ (γ m).V 0 := by
      rw [← hgraph n (T n) (right_mem_Icc.mpr (hT n).le),
        ← hgraph m 0 (left_mem_Icc.mpr (hT m).le)]
      exact B.mono (hcurve n _ (right_mem_Icc.mpr (hT n).le)).1
        (hcurve m _ (left_mem_Icc.mpr (hT m).le)).1 (horder hnm)
    rcases lt_or_gt_of_ne hnm with hnm | hmn
    · exact Ioc_disjoint_Ioc_of_le (ho hnm)
    · exact (Ioc_disjoint_Ioc_of_le (ho hmn)).symm
  have hbudget (n : Fin N) (τ : ℝ) (hτ : τ ∈ Icc 0 (T n)) :
      S.m ((γ n).U τ) ((γ n).V τ) / B.radii n +
        ‖S.theta ((γ n).U τ) ((γ n).V τ) / (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 ≤ E n := by
    have hu := hcurve n τ hτ
    have hm := ((γ n).strictMonoOn_U h.solution).monotoneOn
    have hs := hm (left_mem_Icc.mpr (hT n).le) hτ hτ.1
    have ht := hm hτ (right_mem_Icc.mpr (hT n).le) hτ.2
    rw [(hends n).1] at hs
    rw [(hends n).2] at ht
    have hb := (hE n).2.1 ((γ n).U τ) ⟨hs, ht.trans (B.split n).2⟩
    rwa [hgraph n τ hτ, (γ n).radius τ hτ] at hb
  have hf := hforcing c Λ ε hbox.2.2.1 ui e a b v₀
    (Interaction.terminalScalarSup ui R₀ S) Jstop S vb _ h hab B.cont hJstop B.mem
    (fun u hu => ⟨B.off_axis u hu, (InteractionEstimate.finite_boundary_label_bounds B u hu).1⟩)
    hstop hcore (fun u hu => Interaction.terminal_scalar_le_sup h d.radius_pos
      ⟨(B.mem u hu).1, (B.mem u hu).2.1⟩ (d.annulus u hu))
    hg (Filter.Eventually.of_forall hg0) d.majorant d.budget N B.radii (fun _ => 0) T E γ
    B.radius_pos (fun n => (hT n).le) (fun n => ⟨(hE n).1, hEF n⟩)
    hcurve hdisjU hdisjV hbudget (cylinder_clock_integral_le_budget h B E hE T hT γ hends hgraph)
  rw [hint, hR₀] at hf
  simp only [ct_zeta, Interaction.scalarBackground] at hf ⊢
  convert hf using 1
  apply Finset.sum_congr rfl
  intro n _
  rw [Cylinder.cylinder_covariant_variation h.solution (γ n) (B.radius_pos n) (hT n).le,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg (hT n).le (fun _ _ => norm_nonneg _))]

/-- [internal]
The mixed-clock bound also holds before the last scheduled cylinder or
connector is finished. Each available clock is at most its prescribed
duration; the final radius is only required to lie in the actual stage's
radial range. No next-radius equality is assumed at the partial cutoff.
The coefficient depends only on `H,ρ,χ`, before all scales and stages.
Source: charged_SF_new_version.tex:L4074–L4083. -/
theorem total_boundary_clock_of_duration_le {ui e a b v₀ H ρ χ C ε₀ b₀ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N)
    (hH : 0 < H) (hρ : 0 < ρ ∧ ρ < χ) (hχ : 0 < χ ∧ χ < 1)
    (hC : 0 ≤ C) (he : 0 < ε₀) (hb : 0 < b₀) (σ : ℕ → ℝ)
    (hradii : ∀ n : Fin N, B.radii n = stageRadius ρ b₀ n)
    (T : Fin N → ℝ) (hT : ∀ n, 0 < T n)
    (hshort : ∀ n, T n ≤ stageDuration H ρ b₀ χ C ε₀ σ n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) :
    cylinderClock S vb a b ≤ H * b₀ / (ε₀ * (1 - ρ / χ)) + b₀ := by
  have hfirst (i : Fin (N + 1)) : a ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ b :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hcyl (n : Fin N) : cylinderClock S vb (B.cuts n.castSucc) (B.cool n) = T n := by
    have hsub : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ Icc a b := by
      rw [(hends n).1, (hends n).2]
      exact Icc_subset_Icc (hfirst _) ((B.split n).2.trans (hlast _))
    have hh := integral_clock_pullback hS (hT n) (γ n) vb (fun _ => 1)
      (B.cont.mono hsub) (fun u hu => B.mem u (hsub hu)) (hgraph n) continuousOn_const
    rw [cylinderClock_def]
    simpa only [one_mul, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      (hends n).1, (hends n).2] using hh
  have hcon (n : Fin N) : cylinderClock S vb (B.cool n) (B.cuts n.succ) ≤
      stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1) := by
    have hh := finite_boundary_connector_clock hS B n
    rw [B.cylinder n (B.cool n) ⟨(B.split n).1, le_rfl⟩] at hh
    have hlow := (B.radius_range n (B.cuts n.succ)
      ⟨B.ordered (Fin.castSucc_le_succ n), le_rfl⟩).1
    rw [hradii n] at hh hlow
    have hsucc : stageRadius ρ b₀ (n + 1) = ρ * stageRadius ρ b₀ n := by
      simp only [stageRadius, pow_succ]
      ring
    rw [hh, hsucc]
    linarith only [hlow]
  rw [finite_boundary_clock_eq_sum hS B]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.univ) =>
    add_le_add (show cylinderClock S vb (B.cuts n.castSucc) (B.cool n) ≤
      stageDuration H ρ b₀ χ C ε₀ σ n by rw [hcyl]; exact hshort n) (hcon n))
  apply hsum.trans
  rw [Finset.sum_add_distrib,
    ← Finset.sum_range (fun n => stageDuration H ρ b₀ χ C ε₀ σ n),
    ← Finset.sum_range (fun n => stageRadius ρ b₀ n - stageRadius ρ b₀ (n + 1))]
  exact total_boundary_clock_of_estimates H ρ χ C ε₀ b₀ σ hρ.1.le hb.le
    (total_prescribed_clock H ρ χ C ε₀ b₀ σ hH.le hρ hχ.2 hC he hb) N

/-- [internal]
The boundary clock at a cylinder point equals its actual cylinder parameter,
also at the singleton start. This identifies the clipped variation used in
cutoff continuity with the variation of a restricted actual cylinder.
No prescribed duration or stopping estimate is used. Constants: none. -/
theorem cylinder_clock_at_parameter {ui e R T : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hT : 0 ≤ T)
    (γ : ClockCylinder S (origDomain ui) R 0 T) (vb : ℝ → ℝ)
    (hc : ContinuousOn vb (Icc (γ.U 0) (γ.U T)))
    (hmem : ∀ u ∈ Icc (γ.U 0) (γ.U T), (u, vb u) ∈ origDomain ui)
    (hgraph : ∀ τ ∈ Icc 0 T, vb (γ.U τ) = γ.V τ)
    {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    cylinderClock S vb (γ.U 0) (γ.U τ) = τ := by
  by_cases hzero : τ = 0
  · simp only [hzero, cylinderClock, intervalIntegral.integral_same]
  have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hzero)
  have hmono := (γ.strictMonoOn_U h.solution).monotoneOn
  have hUτ := hmono hτ ⟨hT, le_rfl⟩ hτ.2
  have hsub : Icc (γ.U 0) (γ.U τ) ⊆ Icc (γ.U 0) (γ.U T) :=
    Icc_subset_Icc le_rfl hUτ
  have hp := integral_clock_pullback h.solution hτpos
    (restrictClockCylinder γ 0 τ le_rfl hτ.2) vb (fun _ => 1)
    (hc.mono hsub) (fun u hu => hmem u (hsub hu))
    (fun t ht => hgraph t ⟨ht.1, ht.2.trans hτ.2⟩) continuousOn_const
  simpa only [cylinderClock, restrictClockCylinder_U, one_mul, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one] using hp

/-- [internal]
The actual boundary clock based at any visited cut is nondecreasing on
the entire finite path, including connectors. The density is continuous
and positive there. Constants: none. -/
theorem monotoneOn_cylinderClock {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) {s : ℝ} (hs : s ∈ Icc a b) :
    MonotoneOn (cylinderClock S vb s) (Icc a b) := by
  have hab : a ≤ b := hs.1.trans hs.2
  have cf : ContinuousOn (fun u => -S.nu u (vb u)) (Icc a b) :=
    (h.solution.cont_nu.comp (continuousOn_id.prodMk B.cont) B.mem).neg
  have hi {u v : ℝ} (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
      IntervalIntegrable (fun u => -S.nu u (vb u)) volume u v :=
    (cf.intervalIntegrable_of_Icc (μ := volume) hab).mono_set
      (uIcc_subset_uIcc (by simpa only [uIcc_of_le hab] using hu)
        (by simpa only [uIcc_of_le hab] using hv))
  intro u hu v hv huv
  unfold cylinderClock
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi hs hu) (hi hu hv)]
  apply le_add_of_nonneg_right
  apply intervalIntegral.integral_nonneg huv
  intro x hx
  exact (neg_pos.mpr (h.solution.nu_neg _ (B.mem x ⟨hu.1.trans hx.1, hx.2.trans hv.2⟩))).le

end EmcsfAcExtension.Global.Closure
