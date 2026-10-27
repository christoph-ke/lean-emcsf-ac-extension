module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Cooling.ObservationInput
import EmcsfAcExtension.Global.Cooling.LaterExports
import EmcsfAcExtension.Global.Observation.CylinderClock
import EmcsfAcExtension.Global.Observation.CylinderIdentity
import EmcsfAcExtension.Global.Interaction.ConnectorBudget
import EmcsfAcExtension.Infra.Sequence.EnergyRecurrence
import EmcsfAcExtension.Infra.Sequence.GeometricClock

/-! # Field budgets and numerical sums on finite constructions

Cooling and actual connectors supply the shared boundary budgets on any
available finite path, including a singleton final cylinder. Observation is
an explicit upstream input. Fixed coefficients precede entry energies,
variations, radii and cutoffs. The numerical sums use only the finite prefix.
Source: charged_SF_new_version.tex:L3908–L3931, L4074–L4079; internal project record.
-/

public section

open Finset Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal] The entry energy is an upper envelope chosen before the entry
row, rather than a value defined from that row. -/
@[simp] theorem energyEnvelope_zero (χ C εentry : ℝ) (σ : ℕ → ℝ) :
    energyEnvelope χ C εentry σ 0 = εentry := rfl

/-- [internal] The exact numerical recurrence of charged_SF_new_version.tex:L3908–L3910.
Applying cooling and the connector estimate to actual fields is a separate
obligation; this identity alone closes no recurrence application node. -/
@[simp] theorem energyEnvelope_succ (χ C εentry : ℝ) (σ : ℕ → ℝ) (n : ℕ) :
    energyEnvelope χ C εentry σ (n + 1) =
      χ * energyEnvelope χ C εentry σ n + C * σ n ^ 2 := rfl

/-- [internal] Nonnegativity of every numerical envelope, for arbitrary real
variations. Only the fixed coefficients and entry envelope need be nonnegative. -/
theorem energyEnvelope_nonneg {χ C εentry : ℝ} (hχ : 0 ≤ χ) (hC : 0 ≤ C)
    (he : 0 ≤ εentry) (σ : ℕ → ℝ) (n : ℕ) :
    0 ≤ energyEnvelope χ C εentry σ n := by
  induction n with
  | zero => exact he
  | succ n ih =>
    exact add_nonneg (mul_nonneg hχ ih) (mul_nonneg hC (sq_nonneg _))

/-- [internal] The lower geometric bound in charged_SF_new_version.tex:L3915–L3917.
There is no additive positive energy floor and no upper bound on variations. -/
theorem geometric_le_energyEnvelope {χ C : ℝ} (hχ : 0 ≤ χ) (hC : 0 ≤ C)
    (εentry : ℝ) (σ : ℕ → ℝ) (n : ℕ) :
    χ ^ n * εentry ≤ energyEnvelope χ C εentry σ n := by
  exact geometric_le_of_le_recurrence hχ (energyEnvelope χ C εentry σ) n
    (fun k _ => le_add_of_nonneg_right (mul_nonneg hC (sq_nonneg (σ k)))) n le_rfl

/-- [internal] Every prescribed envelope is strictly positive when the
contraction and entry envelope are positive, independently of stage existence. -/
theorem energyEnvelope_pos {χ C εentry : ℝ} (hχ : 0 < χ) (hC : 0 ≤ C)
    (he : 0 < εentry) (σ : ℕ → ℝ) (n : ℕ) :
    0 < energyEnvelope χ C εentry σ n :=
  (mul_pos (pow_pos hχ n) he).trans_le (geometric_le_energyEnvelope hχ.le hC _ _ _)

/-- [internal] Architecture §3's exact numerical finite-stage sum template.
`Csum` depends only on `χ`, `C`, `Cbudget`, uniformly in entry energy,
variation, finite cutoff and every geometric scale. Actual boundary budgets
must still be proved from cooling and connectors before node eq:cc-budget-sums
can be closed by this helper. The last variation may be truncated. -/
theorem finite_stage_sums (χ C Cbudget : ℝ)
    (hχ : 0 ≤ χ ∧ χ < 1) (hC : 0 ≤ C) (hCb : 0 ≤ Cbudget) :
    ∃ Csum : ℝ, 0 < Csum ∧ ∀ (εentry : ℝ) (σ : ℕ → ℝ) (N : ℕ),
      0 ≤ εentry → (∀ n, 0 ≤ σ n) →
      (∑ n ∈ range N, stageBudget Cbudget χ C εentry σ n) ≤
        Csum * (εentry + (∑ n ∈ range N, σ n) ^ 2) ∧
      (∑ n ∈ range N, Real.sqrt (stageBudget Cbudget χ C εentry σ n)) ≤
        Csum * (Real.sqrt εentry + ∑ n ∈ range N, σ n) := by
  obtain ⟨B, hB, hsum⟩ := exists_budget_constant_of_lt_one hχ.1 hχ.2 hC hCb
  refine ⟨B, hB, ?_⟩
  intro εentry σ N he hs
  exact hsum (energyEnvelope χ C εentry σ) σ (stageBudget Cbudget χ C εentry σ) N
    (fun n _ => energyEnvelope_nonneg hχ.1 hC he σ n) (fun n _ => hs n)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)

/-- [internal] The prescribed clock is positive for positive fixed clock
coefficient, contraction, radius and entry envelope. Thus its real denominator
never vanishes; no availability of a cylinder is asserted. -/
theorem stageDuration_pos {H ρ b₀ χ C εentry : ℝ} (hH : 0 < H) (hρ : 0 < ρ)
    (hb : 0 < b₀) (hχ : 0 < χ) (hC : 0 ≤ C) (he : 0 < εentry)
    (σ : ℕ → ℝ) (n : ℕ) :
    0 < stageDuration H ρ b₀ χ C εentry σ n :=
  div_pos (mul_pos hH (mul_pos (pow_pos hρ n) hb))
    (energyEnvelope_pos hχ hC he σ n)

/-- [internal] The internal project record prescribed-clock template, with no
variation hypothesis. The fixed coefficients precede all radii, envelopes,
variations and cutoffs. This numerical estimate is not stage existence. -/
theorem total_prescribed_clock (H ρ χ C εentry b₀ : ℝ) (σ : ℕ → ℝ)
    (hH : 0 ≤ H) (hρ : 0 < ρ ∧ ρ < χ) (_hχ : χ < 1) (hC : 0 ≤ C)
    (he : 0 < εentry) (hb : 0 < b₀) :
    ∀ N : ℕ, (∑ n ∈ range N, stageDuration H ρ b₀ χ C εentry σ n) ≤
      H * b₀ / (εentry * (1 - ρ / χ)) := by
  intro N
  exact sum_cylinder_clock_le_of_geometric_le hρ.1.le (hρ.1.trans hρ.2) hρ.2 hH
    b₀ εentry (energyEnvelope χ C εentry σ) N hb.le he
    (fun n _ => geometric_le_energyEnvelope (hρ.1.trans hρ.2).le hC εentry σ n)

end EmcsfAcExtension.Global.Closure

namespace EmcsfAcExtension.Global.Closure

/-- [internal] Actual cylindrical field budgets on every partial stage,
including singleton and shorter-than-window intervals. Observation is the
literal pending architecture proposition; the energy identity and endpoint
strip estimates are discharged by the landed cooling theorem. The constant
is chosen from the fixed gap before all solution data, radii, energy
envelopes, intervals and variations. Source: charged_SF_new_version.tex:L3919–L3932. -/
theorem partial_stage_budgets_of_estimates (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hobs : Cooling.observationInput δ) :
    ∃ Tstar δstar ηstar Cbudget : ℝ,
      0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧ 0 < Cbudget ∧
      ∀ (ui e b s t ε : ℝ) (S : Fields),
      0 < b → s < t → 0 ≤ ε → OriginalData ui e S →
      ∀ γ : ClockCylinder S (origDomain ui) b s t,
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
      (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
      (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
        triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
        (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
      cylinderEnergy S b (γ.U s) (γ.V s) / b ≤ ε →
      ∀ p ∈ Icc s t,
      let σ := (curveCovVar e S S.a γ.U γ.V s p).toReal
      (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
        ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc s p) +
        (∫ x in s..p,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
        Cbudget * (ε + σ ^ 2)) := by
  obtain ⟨Ts, _, δs, ηs, C, hTs, _, hδs, _, hηs, hC, hbudget⟩ :=
    Cooling.subinterval_budgets_of_observation δ hδ hobs
  refine ⟨Ts, δs, ηs, C, hTs, hδs, hηs, hC, ?_⟩
  intro ui e b s t ε S hb hst _he h γ hac hweak hwindows hentry p hp
  have hbound := (hbudget ui e b s t S hb hst h γ hac hweak hwindows s
    (left_mem_Icc.mpr hst.le) p hp).2
  exact hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hentry le_rfl) hC.le)

/-- [internal] Convert an actual cylinder budget from its clock to the
incoming label used by `BoundaryBudgets`. The graph identity is everywhere,
and the integrand is a continuous field expression on this proper path.
The coefficient is exactly `1`, independent of the cylinder or duration. -/
theorem integral_clock_pullback {e b s t : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hst : s < t) (γ : ClockCylinder S D b s t)
    (vb f : ℝ → ℝ) (hvb : ContinuousOn vb (Icc (γ.U s) (γ.U t)))
    (hmem : ∀ u ∈ Icc (γ.U s) (γ.U t), (u, vb u) ∈ D)
    (hgraph : ∀ τ ∈ Icc s t, vb (γ.U τ) = γ.V τ)
    (hf : ContinuousOn f (Icc (γ.U s) (γ.U t))) :
    (∫ u in γ.U s..γ.U t, f u * (-S.nu u (vb u))) =
      ∫ τ in s..t, f (γ.U τ) := by
  have hm := (γ.strictMonoOn_U hS).monotoneOn
  have hmap : Set.MapsTo γ.U (Icc s t) (Icc (γ.U s) (γ.U t)) := by
    intro τ hτ
    exact ⟨hm (left_mem_Icc.mpr hst.le) hτ hτ.1,
      hm hτ (right_mem_Icc.mpr hst.le) hτ.2⟩
  have hcont := (hS.cont_nu.comp (continuousOn_id.prodMk hvb) hmem).neg
  have hg := hf.mul hcont
  have hrate : ContinuousOn (fun τ => (-S.nu (γ.U τ) (γ.V τ))⁻¹) (uIcc s t) := by
    rw [uIcc_of_le hst.le]
    exact (γ.continuousOn_trace hS.cont_nu).neg.inv₀ (fun τ hτ =>
      neg_ne_zero.mpr (hS.nu_neg _ (γ.mem τ hτ)).ne)
  have hchange := intervalIntegral.integral_comp_mul_deriv''
    (show ContinuousOn γ.U (uIcc s t) by simpa only [uIcc_of_le hst.le] using γ.c1_U.continuousOn)
    (fun τ hτ => (γ.hasDerivAt_U (by
      simpa only [min_eq_left hst.le, max_eq_right hst.le] using hτ)).hasDerivWithinAt)
    hrate (hg.mono (by
      rintro u ⟨τ, hτ, rfl⟩
      exact hmap (by simpa only [uIcc_of_le hst.le] using hτ)))
  have hchange' :
      (∫ τ in s..t, (f (γ.U τ) * (-S.nu (γ.U τ) (vb (γ.U τ)))) *
        (-S.nu (γ.U τ) (γ.V τ))⁻¹) =
      ∫ u in γ.U s..γ.U t, f u * (-S.nu u (vb u)) := hchange
  rw [← hchange']
  apply intervalIntegral.integral_congr
  intro τ hτ
  have hτ' : τ ∈ Icc s t := by simpa only [uIcc_of_le hst.le] using hτ
  dsimp only [Function.comp_def]
  rw [hgraph τ hτ']
  have hn : S.nu (γ.U τ) (γ.V τ) ≠ 0 := (hS.nu_neg _ (γ.mem τ hτ')).ne
  field_simp [hn]

/-- [internal] Glue actual cylinder and connector estimates into the
shared interaction interface. Both pieces use the preceding cylinder's
budget; the fixed connector factor is absorbed once, before the finite
path. No interaction estimate is used to generate its own input budgets. -/
theorem boundary_budgets_of_piece_estimates (K : ℝ) (hK : 0 ≤ K)
    {ui e u₀ u₁ v₀ ρ : ℝ} {S : Fields} {vb : ℝ → ℝ} {N : ℕ}
    (h : OriginalData ui e S) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (E : Fin N → ℝ) (hE : ∀ n, 0 ≤ E n)
    (hcyl : ∀ n,
      (∀ u ∈ Icc (B.cuts n.castSucc) (B.cool n),
        S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ E n) ∧
      (∫ u in (B.cuts n.castSucc)..(B.cool n),
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) ≤ E n)
    (hcon : ∀ n,
      (∀ u ∈ Icc (B.cool n) (B.cuts n.succ),
        S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ K * E n) ∧
      (∫ u in (B.cool n)..(B.cuts n.succ),
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) ≤ K * E n) :
    BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B (fun n => (1 + K) * E n) := by
  intro n
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hsub : Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ :=
    Icc_subset_Icc (hfirst _) (hlast _)
  have hmem (u : ℝ) (hu : u ∈ Icc (B.cuts n.castSucc) (B.cuts n.succ)) :=
    B.mem u (hsub hu)
  have cν := h.solution.cont_nu.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have clam := h.solution.cont_lam.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have cθ := h.solution.cont_theta.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have cξ := h.solution.cont_xi.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have cr := h.solution.cont_r.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have cm := h.solution.cont_m.comp (continuousOn_id.prodMk (B.cont.mono hsub)) hmem
  have hr (u : ℝ) (hu : u ∈ Icc (B.cuts n.castSucc) (B.cuts n.succ)) :=
    h.solution.r_pos _ (hmem u hu) (B.off_axis u (hsub hu))
  have cy := cθ.div (Complex.continuous_ofReal.comp_continuousOn clam)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (hmem u hu)).ne')
  have cz := cξ.div (Complex.continuous_ofReal.comp_continuousOn cν)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (hmem u hu)).ne)
  have cμ : ContinuousOn (fun u => S.mu u (vb u)) (Icc (B.cuts n.castSucc) (B.cuts n.succ)) :=
    (continuousOn_const.mul cm).div cr (fun u hu => (hr u hu).ne')
  have cf := ((((cy.norm.pow 2).add (cz.norm.pow 2)).add (cμ.pow 2)).mul cν.neg).div cr
    (fun u hu => (hr u hu).ne')
  have hab := (B.split n).1.trans (B.split n).2
  let cost := fun u =>
    (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
     ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
      (-S.nu u (vb u)) / S.r u (vb u)
  have hi : IntervalIntegrable cost volume (B.cuts n.castSucc) (B.cuts n.succ) :=
    cf.intervalIntegrable_of_Icc (μ := volume) hab
  have hi₁ := hi.mono_set (by
    rw [uIcc_of_le (B.split n).1, uIcc_of_le hab]
    exact Icc_subset_Icc_right (B.split n).2)
  have hi₂ := hi.mono_set (by
    rw [uIcc_of_le (B.split n).2, uIcc_of_le hab]
    exact Icc_subset_Icc_left (B.split n).1)
  refine ⟨mul_nonneg (by positivity) (hE n), ?_, ?_⟩
  · intro u hu
    rcases le_total u (B.cool n) with hc | hc
    · exact ((hcyl n).1 u ⟨hu.1, hc⟩).trans (by
        have hk := mul_nonneg hK (hE n)
        nlinarith only [hk])
    · exact ((hcon n).1 u ⟨hc, hu.2⟩).trans (by
        have he := hE n
        nlinarith only [he])
  · change (∫ u in (B.cuts n.castSucc)..(B.cuts n.succ), cost u) ≤ (1 + K) * E n
    rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
    dsimp only [cost]
    have hc := (hcyl n).2
    have hk := (hcon n).2
    nlinarith only [hc, hk]

/-- [internal] Transfer the actual clock budget to the cylinder's graph.
The consumer supplies `hbudget` by the preceding observation/cooling
application. All coefficients are exactly one; compact bounds used for
integrability depend only on this proper cylinder. -/
theorem cylinder_budget_on_graph_of_estimates {ui e b T E : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hb : 0 < b) (hT : 0 < T)
    (γ : ClockCylinder S (origDomain ui) b 0 T) (vb : ℝ → ℝ)
    (hvb : ContinuousOn vb (Icc (γ.U 0) (γ.U T)))
    (hmem : ∀ u ∈ Icc (γ.U 0) (γ.U T), (u, vb u) ∈ origDomain ui)
    (hoff : ∀ u ∈ Icc (γ.U 0) (γ.U T), u < vb u)
    (hgraph : ∀ τ ∈ Icc 0 T, vb (γ.U τ) = γ.V τ)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T)
    (hbudget : sSup ((fun τ => S.m (γ.U τ) (γ.V τ) / b +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2) '' Icc 0 T) +
      (∫ τ in 0..T,
        (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         S.mu (γ.U τ) (γ.V τ) ^ 2 +
         (cylinderEnergy S b (γ.U τ) (γ.V τ) / b) ^ 2) / b) ≤ E) :
    (∀ u ∈ Icc (γ.U 0) (γ.U T), S.m u (vb u) / S.r u (vb u) +
      ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ E) ∧
    (∫ u in γ.U 0..γ.U T,
      (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
       ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
        (-S.nu u (vb u)) / S.r u (vb u)) ≤ E := by
  let p := fun τ => S.m (γ.U τ) (γ.V τ) / b +
    ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2
  let k := fun τ => (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
    ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
    S.mu (γ.U τ) (γ.V τ) ^ 2) / b
  let q := fun τ => cylinderEnergy S b (γ.U τ) (γ.V τ) / b
  obtain ⟨cy, cz, cμ⟩ := Cylinder.continuousOn_normalized_traces h.solution γ
  have cp : ContinuousOn p (Icc 0 T) :=
    ((γ.continuousOn_trace h.solution.cont_m).div_const b).add (cy.norm.pow 2)
  have ck : ContinuousOn k (Icc 0 T) :=
    (((cy.norm.pow 2).add (cz.norm.pow 2)).add (cμ.pow 2)).div_const b
  have cq : ContinuousOn q (Icc 0 T) := by
    simpa only [q, uIcc_of_le hT.le] using
      (charged_cool_identity ui e b 0 T S h hb hT γ hac).1.continuousOn
  have hnonneg : 0 ≤ ∫ τ in 0..T, (k τ + q τ ^ 2 / b) :=
    intervalIntegral.integral_nonneg hT.le (fun τ _ => by dsimp only [k]; positivity)
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc 0 T) : p τ ≤ sSup (p '' Icc 0 T) :=
    le_csSup (isCompact_Icc.bddAbove_image cp) ⟨τ, hτ, rfl⟩
  have hpn : 0 ≤ p 0 := by
    have hμ := (h.mu _ (γ.mem 0 (left_mem_Icc.mpr hT.le))).1
    have heq : S.m (γ.U 0) (γ.V 0) / b = S.mu (γ.U 0) (γ.V 0) / 2 := by
      simp only [Fields.mu, γ.radius 0 (left_mem_Icc.mpr hT.le)]; ring
    dsimp only [p]
    rw [heq]
    positivity
  have hsupn : 0 ≤ sSup (p '' Icc 0 T) := hpn.trans (hpoint 0 (left_mem_Icc.mpr hT.le))
  have hbudget' : sSup (p '' Icc 0 T) + (∫ τ in 0..T, k τ + q τ ^ 2 / b) ≤ E := by
    convert hbudget using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro τ _
    dsimp only [k, q]; ring
  have hsuple : sSup (p '' Icc 0 T) ≤ E := by linarith only [hbudget', hnonneg]
  have hkint : (∫ τ in 0..T, k τ) ≤ E := by
    have hm := intervalIntegral.integral_mono_on hT.le
      (ck.intervalIntegrable_of_Icc (μ := volume) hT.le)
      ((ck.add ((cq.pow 2).div_const b)).intervalIntegrable_of_Icc (μ := volume) hT.le)
      (fun τ _ => le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hb.le))
    have hm' : (∫ τ in 0..T, k τ) ≤ ∫ τ in 0..T, k τ + q τ ^ 2 / b := hm
    linarith only [hm', hbudget', hsupn]
  constructor
  · intro u hu
    obtain ⟨τ, hτ, hτu⟩ := intermediate_value_Icc hT.le γ.c1_U.continuousOn hu
    have hh := (hpoint τ hτ).trans hsuple
    dsimp only [p] at hh
    simpa only [← hτu, hgraph τ hτ, γ.radius τ hτ] using hh
  · let f := fun u => (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
        ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) / S.r u (vb u)
    have cn := h.solution.cont_nu.comp (continuousOn_id.prodMk hvb) hmem
    have cl := h.solution.cont_lam.comp (continuousOn_id.prodMk hvb) hmem
    have ct := h.solution.cont_theta.comp (continuousOn_id.prodMk hvb) hmem
    have cx := h.solution.cont_xi.comp (continuousOn_id.prodMk hvb) hmem
    have cr := h.solution.cont_r.comp (continuousOn_id.prodMk hvb) hmem
    have cm := h.solution.cont_m.comp (continuousOn_id.prodMk hvb) hmem
    have hr u hu := h.solution.r_pos _ (hmem u hu) (hoff u hu)
    have cy' := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (hmem u hu)).ne')
    have cz' := cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
      (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (hmem u hu)).ne)
    have cμ' : ContinuousOn (fun u => S.mu u (vb u)) (Icc (γ.U 0) (γ.U T)) :=
      (continuousOn_const.mul cm).div cr (fun u hu => (hr u hu).ne')
    have cf : ContinuousOn f (Icc (γ.U 0) (γ.U T)) :=
      ((((cy'.norm.pow 2).add (cz'.norm.pow 2)).add (cμ'.pow 2)).div cr (fun u hu => (hr u hu).ne'))
    have heq := integral_clock_pullback h.solution hT γ vb f hvb hmem hgraph cf
    have heq' : (∫ u in γ.U 0..γ.U T,
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) = ∫ τ in 0..T, k τ := by
      convert heq using 1
      · apply intervalIntegral.integral_congr
        intro u _
        dsimp only [f]; ring
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have hτ' : τ ∈ Icc 0 T := by simpa only [uIcc_of_le hT.le] using hτ
        dsimp only [f, k]
        rw [hgraph τ hτ', γ.radius τ hτ']
    exact heq'.trans_le hkint

/-- [internal] Finite field budgets from observation/cooling and actual
connectors. The finite geometric path and its available clock cylinders
are source data; initial energies are supplied by the recurrence.
The sole pending proposition is observation. Its thresholds precede the
weak stops and connector ratio. The budget coefficient depends only on
`δ,ρ,εweak` and observation, before every solution, energy envelope,
entry scale, finite cutoff or partial last cylinder. This is the exact
`BoundaryBudgets` shape consumed by interaction and internal project record. -/
theorem finite_stage_budgets_of_estimates (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hobs : Cooling.observationInput δ) :
    ∃ Tstar δstar ηstar : ℝ, 0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧
      ∀ (εweak ρ : ℝ), 0 ≤ εweak → 0 < ρ → ∃ Cbudget > 0,
      ∀ (χ C εentry c Λ F ui e u₀ u₁ v₀ Bterm Jstop R₀ : ℝ)
        (S : Fields) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      0 ≤ χ → 0 ≤ C → 0 ≤ εentry → 0 < c → 0 ≤ F → F < 1 → 0 ≤ Jstop →
      OriginalData ui e S → (∀ n, 0 ≤ T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n, AbsolutelyContinuousOnInterval (curveParallel e S S.a (γ n).U (γ n).V 0) 0 (T n)) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C εentry σ n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), S.mu ((γ n).U τ) ((γ n).V τ) +
        ‖S.theta ((γ n).U τ) ((γ n).V τ) / (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ≤ δstar) →
      (∀ n, ∀ τ ∈ Icc (Tstar * B.radii n) (T n - Tstar * B.radii n),
        triangle ((γ n).U (τ - Tstar * B.radii n))
          ((γ n).V (τ + Tstar * B.radii n)) ⊆ origDomain ui ∧
        (∀ p ∈ triangle ((γ n).U (τ - Tstar * B.radii n)) ((γ n).V (τ + Tstar * B.radii n)),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        |e| * B.radii n * (1 + ‖S.a ((γ n).U τ) ((γ n).V τ)‖) ≤ ηstar) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      (∀ u ∈ Icc u₀ u₁, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc u₀ u₁, ‖S.phi u 0‖ ≤ Bterm) → (∀ n, B.radii n ≤ R₀) →
      ∀ g : Fin N → ℝ → ℝ,
      (∀ n, IntegrableOn (g n) (Icc (vb (B.cool n)) 0)) →
      (∀ n, ∀ᵐ w ∂volume.restrict (Icc (vb (B.cool n)) 0), 0 ≤ g n w) →
      (∀ n, ∀ u ∈ Icc (B.cool n) (B.cuts n.succ),
        ∀ᵐ w ∂volume.restrict (Icc (vb (B.cool n)) 0), ‖weightedJ S u w‖ ≤ g n w) →
      (∀ n, (∫ w in vb (B.cool n)..0, g n w) ≤ Jstop) →
      e ^ 2 * (1 + Bterm + (F + c⁻¹ * Jstop) / (1 - F ^ 2)) ^ 2 * R₀ ^ 2 ≤ 1 →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B
        (fun n => stageBudget Cbudget χ C εentry σ n) := by
  obtain ⟨Ts, δs, ηs, Cb, hTs, hδs, hηs, hCb, hcool⟩ :=
    partial_stage_budgets_of_estimates δ hδ hobs
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ hεweak hρ
  obtain ⟨K, hK, hconnect⟩ := Interaction.connector_budget δ ρ εweak hδ.1 hδ.2.le hρ hεweak
  refine ⟨(1 + K) * (Cb + 2), by positivity, ?_⟩
  intro χ C εentry c Λ F ui e u₀ u₁ v₀ Bterm Jstop R₀ S vb σ N B T
    hχ hC he hc hF hF1 hJ h hT γ hends hgraph hac hσ henergy hweak hwindows
    hstop hcore hterm hR g hg hg0 hmajor hJg hscale
  let E := fun n : Fin N => (Cb + 2) * (energyEnvelope χ C εentry σ n + σ n ^ 2)
  have hE (n : Fin N) : 0 ≤ E n :=
    mul_nonneg (by positivity) (add_nonneg (energyEnvelope_nonneg hχ hC he σ n) (sq_nonneg _))
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hstage (n : Fin N) : Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ :=
    Icc_subset_Icc (hfirst _) (hlast _)
  have hcyl' (n : Fin N) :
      (∀ u ∈ Icc (B.cuts n.castSucc) (B.cool n),
        S.m u (vb u) / S.r u (vb u) + ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ E n) ∧
      (∫ u in (B.cuts n.castSucc)..(B.cool n),
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) ≤ E n := by
    rcases eq_or_lt_of_le (hT n) with hz | ht
    · have hcool : B.cool n = B.cuts n.castSucc :=
        (hends n).2.symm.trans ((congrArg (γ n).U hz.symm).trans (hends n).1)
      have hp := (γ n).mem 0 (left_mem_Icc.mpr (hT n))
      have hμ := (h.mu _ hp).1
      have hlog := Real.log_le_sub_one_of_pos (h.solution.one_sub_mu_pos _ hp)
      have hq : cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n =
          (‖S.theta ((γ n).U 0) ((γ n).V 0) /
            (S.lam ((γ n).U 0) ((γ n).V 0) : ℂ)‖ ^ 2 -
              Real.log (1 - S.mu ((γ n).U 0) ((γ n).V 0))) / 2 := by
        unfold cylinderEnergy
        field_simp [(B.radius_pos n).ne']
      have hm : S.m ((γ n).U 0) ((γ n).V 0) / S.r ((γ n).U 0) ((γ n).V 0) =
          S.mu ((γ n).U 0) ((γ n).V 0) / 2 := by unfold Fields.mu; ring
      have hpE : S.m ((γ n).U 0) ((γ n).V 0) / S.r ((γ n).U 0) ((γ n).V 0) +
          ‖S.theta ((γ n).U 0) ((γ n).V 0) /
            (S.lam ((γ n).U 0) ((γ n).V 0) : ℂ)‖ ^ 2 ≤
            2 * energyEnvelope χ C εentry σ n := by
        have hpoint : S.m ((γ n).U 0) ((γ n).V 0) / S.r ((γ n).U 0) ((γ n).V 0) +
            ‖S.theta ((γ n).U 0) ((γ n).V 0) /
              (S.lam ((γ n).U 0) ((γ n).V 0) : ℂ)‖ ^ 2 ≤
              2 * (cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n) := by
          rw [hm, hq]
          linarith only [hlog, hμ]
        exact hpoint.trans (mul_le_mul_of_nonneg_left (henergy n) (by norm_num))
      have hElarge : 2 * energyEnvelope χ C εentry σ n ≤ E n := by
        have hn := energyEnvelope_nonneg hχ hC he σ n
        have h₁ := mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ Cb + 2 by linarith only [hCb]) hn
        exact h₁.trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (sq_nonneg (σ n))) (by positivity))
      constructor
      · intro u hu
        rw [hcool] at hu
        have hu' : u = B.cuts n.castSucc := le_antisymm hu.2 hu.1
        have hh := hpE.trans hElarge
        simpa only [← hgraph n 0 (left_mem_Icc.mpr (hT n)), (hends n).1, hu'] using hh
      · rw [hcool, intervalIntegral.integral_same]
        exact hE n
    · have hsub : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ Icc u₀ u₁ := by
        rw [(hends n).1, (hends n).2]
        exact Icc_subset_Icc (hfirst _) ((B.split n).2.trans (hlast _))
      have hraw := hcool ui e (B.radii n) 0 (T n) (energyEnvelope χ C εentry σ n) S
        (B.radius_pos n) ht (energyEnvelope_nonneg hχ hC he σ n) h (γ n) (hac n) (hweak n)
        (by simpa only [zero_add] using hwindows n) (henergy n) (T n) (right_mem_Icc.mpr ht.le)
      rw [← hσ n] at hraw
      have hrawE := hraw.trans (mul_le_mul_of_nonneg_right (show Cb ≤ Cb + 2 by linarith)
        (add_nonneg (energyEnvelope_nonneg hχ hC he σ n) (sq_nonneg (σ n))))
      have hh := cylinder_budget_on_graph_of_estimates (E := E n) h (B.radius_pos n) ht (γ n) vb
        (B.cont.mono hsub) (fun u hu => B.mem u (hsub hu)) (fun u hu => B.off_axis u (hsub hu))
        (hgraph n) (hac n) hrawE
      simpa only [(hends n).1, (hends n).2] using hh
  have hcon (n : Fin N) :
      (∀ u ∈ Icc (B.cool n) (B.cuts n.succ),
        S.m u (vb u) / S.r u (vb u) + ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ K * E n) ∧
      (∫ u in (B.cool n)..(B.cuts n.succ),
        (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
         ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
          (-S.nu u (vb u)) / S.r u (vb u)) ≤ K * E n := by
    have hsub : Icc (B.cool n) (B.cuts n.succ) ⊆ Icc u₀ u₁ :=
      Icc_subset_Icc ((hfirst _).trans (B.split n).1) (hlast _)
    have hcoolmem := hsub (left_mem_Icc.mpr (B.split n).2)
    have hendmem := hsub (right_mem_Icc.mpr (B.split n).2)
    have hstart := B.cylinder n (B.cool n) ⟨(B.split n).1, le_rfl⟩
    have hinit := (hcyl' n).1 (B.cool n) ⟨(B.split n).1, le_rfl⟩
    rw [hstart] at hinit
    have hlocal : ExteriorStops S
        (exteriorDomain ui (B.cool n) (B.cuts n.succ) (fun _ => vb (B.cool n))) δ c Λ F εweak := by
      intro p hp
      have hu := hsub ⟨hp.2.1, hp.2.2.1⟩
      have hlower : vb p.1 ≤ p.2 := by
        rw [B.connector n p.1 ⟨hp.2.1, hp.2.2.1⟩]
        exact hp.2.2.2
      exact hstop p ⟨hp.1, hu.1, hu.2, hlower⟩
    have hp := B.mem _ hcoolmem
    have hcb := B.connector n (B.cuts n.succ) ⟨(B.split n).2, le_rfl⟩
    have hconn := hconnect c Λ F hc hF hF1 ui e (B.cool n) (B.cuts n.succ)
      (vb (B.cool n)) (B.radii n) (E n) Bterm Jstop R₀ S (g n) h (B.split n).2 hp.1
      (by simpa only [hcb] using B.off_axis _ hendmem) hp.2.2.2 hJ (B.radius_pos n) (hR n)
      (hE n) hstart hinit (fun u hu => by
        have hh := (B.radius_range n u ⟨(B.split n).1.trans hu.1, hu.2⟩).1
        simpa only [B.connector n u hu] using hh) hlocal
      (fun u hu => hcore u (hsub hu)) (fun u hu => hterm u (hsub hu))
      (hg n) (hg0 n) (hmajor n) (hJg n) hscale
    constructor
    · intro u hu
      simpa only [B.connector n u hu] using (hconn u hu).1
    · have hh := (hconn _ (right_mem_Icc.mpr (B.split n).2)).2.1
      convert hh using 1
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (B.cool n) (B.cuts n.succ) := by
        simpa only [uIcc_of_le (B.split n).2] using hu
      dsimp only
      rw [B.connector n u hu']
  have hbud := boundary_budgets_of_piece_estimates K hK.le h B E hE hcyl' hcon
  convert hbud using 1
  ext n
  dsimp only [stageBudget, E]
  ring

end EmcsfAcExtension.Global.Closure

namespace EmcsfAcExtension.Global

/-- [node eq:cc-budget-sums]
Sum the prescribed budgets that `Closure.finite_stage_budgets_of_estimates`
produces for the actual finite field path, including a partial last stage.
The positive coefficient depends only on `χ,C,Cbudget`, before the entry
energy, variation sequence and cutoff; no geometric scale enters it.
Source: charged_SF_new_version.tex:L3924–L3929. -/
theorem cc_budget_sums (χ C Cbudget : ℝ)
    (hχ : 0 ≤ χ ∧ χ < 1) (hC : 0 ≤ C) (hCb : 0 ≤ Cbudget) :
    ∃ Csum : ℝ, 0 < Csum ∧ ∀ (εentry : ℝ) (σ : ℕ → ℝ) (N : ℕ),
      0 ≤ εentry → (∀ n < N, 0 ≤ σ n) →
      (∑ n ∈ Finset.range N, stageBudget Cbudget χ C εentry σ n) ≤
        Csum * (εentry + (∑ n ∈ Finset.range N, σ n) ^ 2) ∧
      (∑ n ∈ Finset.range N, Real.sqrt (stageBudget Cbudget χ C εentry σ n)) ≤
        Csum * (Real.sqrt εentry + ∑ n ∈ Finset.range N, σ n) := by
  obtain ⟨B, hB, hsum⟩ := exists_budget_constant_of_lt_one hχ.1 hχ.2 hC hCb
  refine ⟨B, hB, ?_⟩
  intro εentry σ N he hs
  exact hsum (energyEnvelope χ C εentry σ) σ (stageBudget Cbudget χ C εentry σ) N
    (fun n _ => Closure.energyEnvelope_nonneg hχ.1 hC he σ n) hs
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)

end EmcsfAcExtension.Global
