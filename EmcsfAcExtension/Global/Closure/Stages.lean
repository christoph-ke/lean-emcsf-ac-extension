module

public import EmcsfAcExtension.Global.Closure.StageSums
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Closure.Parameters
public import EmcsfAcExtension.Global.Closure.Entry
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Interaction.PairKernel
import EmcsfAcExtension.Global.Calculus.Endpoint
public import EmcsfAcExtension.Global.Cooling.ObservationInput
import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Global.Interaction.ConnectorBudget
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Infra.AC.Variation

/-! # Available finite paths and their actual field energies

Construct and transport available finite cylinder/connector paths. Actual
cooling and connector laws propagate the cut energies by induction before
producing the shared field budgets and their sums. Observation remains the
explicit upstream input; existence of all stages is not assumed.
Source: charged_SF_new_version.tex:L3899–L3932.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [internal] Restrict an available cylinder to any smaller clock interval.
Both physical labels, the radius, and the two clock rates are preserved.
This constructs a partial stage without assuming that a full stage exists. -/
@[expose] def restrictClockCylinder {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (s' t' : ℝ) (hs : s ≤ s') (ht : t' ≤ t) :
    ClockCylinder S D b s' t' where
  U := γ.U
  V := γ.V
  c1_U := γ.c1_U.mono (Icc_subset_Icc hs ht)
  c1_V := γ.c1_V.mono (Icc_subset_Icc hs ht)
  mem := fun x hx => γ.mem x (Icc_subset_Icc hs ht hx)
  radius := fun x hx => γ.radius x (Icc_subset_Icc hs ht hx)
  rate_U := fun x hx => (γ.rate_U x (Icc_subset_Icc hs ht hx)).mono (Icc_subset_Icc hs ht)
  rate_V := fun x hx => (γ.rate_V x (Icc_subset_Icc hs ht hx)).mono (Icc_subset_Icc hs ht)

/-- [internal] Restricting a clock cylinder preserves its incoming label. -/
@[simp] theorem restrictClockCylinder_U {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (s' t' : ℝ) (hs : s ≤ s') (ht : t' ≤ t) :
    (restrictClockCylinder γ s' t' hs ht).U = γ.U := rfl

/-- [internal] Restricting a clock cylinder preserves its outgoing label. -/
@[simp] theorem restrictClockCylinder_V {S : Fields} {D : Set (ℝ × ℝ)} {b s t : ℝ}
    (γ : ClockCylinder S D b s t) (s' t' : ℝ) (hs : s ≤ s') (ht : t' ≤ t) :
    (restrictClockCylinder γ s' t' hs ht).V = γ.V := rfl

/-- [internal] The current envelope uses only earlier variations.
Truncating the last cylinder's variation, or extending a finite variation
sequence by zero, preserves all already prescribed initial energies.
Constants: none; no future stage is required. -/
theorem energyEnvelope_congr_before (χ C εentry : ℝ) (σ τ : ℕ → ℝ)
    (n : ℕ) (heq : ∀ k < n, σ k = τ k) :
    energyEnvelope χ C εentry σ n = energyEnvelope χ C εentry τ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [energyEnvelope_succ, energyEnvelope_succ,
      ih (fun k hk => heq k (Nat.lt_succ_of_lt hk)), heq n (Nat.lt_succ_self n)]


/-- [internal] An actual incoming connector reaches each smaller positive
radius before its existing axis endpoint. Every partial connector has the
prescribed radial range. No stopping improvement or stage-existence
hypothesis is used. Constants: none. -/
theorem exists_connector {ui e a v B ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hav : a < v) (hv : v < 0)
    (hB : 0 < B) (hρ : 0 < ρ ∧ ρ < 1) (hstart : S.r a v = B) :
    ∃ b ∈ Ioo a v, S.r b v = ρ * B ∧
      (∀ u ∈ Icc a b, (u, v) ∈ origDomain ui ∧
        ρ * B ≤ S.r u v ∧ S.r u v ≤ B) ∧
      cylinderClock S (fun _ => v) a b = (1 - ρ) * B := by
  have hs : inSeg a v v ⊆ origDomain ui := by
    rintro ⟨u, w⟩ ⟨hu, huv, rfl⟩
    exact ⟨hia.trans hu, huv.trans_lt hv, huv, hv.le⟩
  have hc := Calculus.continuousOn_in_section h.solution.cont_r hs
  have haxis : S.r v v = 0 := (h.solution.axis v (hs ⟨hav.le, le_rfl, rfl⟩)).1
  have hρB : 0 < ρ * B := mul_pos hρ.1 hB
  have hltB : ρ * B < B := mul_lt_of_lt_one_left hB hρ.2
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc' hav.le hc
    (show ρ * B ∈ Icc (S.r v v) (S.r a v) by rw [haxis, hstart]; exact ⟨hρB.le, hltB.le⟩)
  have hab : a < b := by
    by_contra hn
    have he : b = a := le_antisymm (le_of_not_gt hn) hb.1
    have hh : B = ρ * B := by simpa only [he, hstart] using heq
    exact hltB.ne hh.symm
  have hbv : b < v := by
    by_contra hn
    have he : b = v := le_antisymm hb.2 (le_of_not_gt hn)
    have hh : 0 = ρ * B := by simpa only [he, haxis] using heq
    exact hρB.ne hh
  have hanti := (InteractionEstimate.incoming_radius_calculus h.solution hav.le le_rfl hs).2
  have hseg : inSeg a b v ⊆ origDomain ui :=
    fun p hp => hs ⟨hp.1, hp.2.1.trans hb.2, hp.2.2⟩
  refine ⟨b, ⟨hab, hbv⟩, heq, ?_, ?_⟩
  · intro u hu
    refine ⟨hseg ⟨hu.1, hu.2, rfl⟩, ?_, ?_⟩
    · rw [← heq]
      exact hanti ⟨hu.1, hu.2.trans hb.2⟩ hb hu.2
    · rw [← hstart]
      exact hanti ⟨le_rfl, hav.le⟩ ⟨hu.1, hu.2.trans hb.2⟩ hu.1
  · have hr := (Calculus.in_integralForm h.solution hab.le hbv.le hseg).1
    simp only [cylinderClock, intervalIntegral.integral_neg, ← hr.2, hstart, heq]
    ring

/-- [node sec:charged-closure#stage-path]
Prescribe each available stage with the exact geometric radius and finite
clock, identify its covariant variation with the integral of the parallel
AC derivative, and construct its incoming connector to the next radius.
The available cylinder is quantified after the schedule; this asserts no
availability beyond the current positive-radius portion. Constants `H,ρ,χ,C`
precede the entry scale and every stage. Source: charged_SF_new_version.tex:L3899–L3907. -/
theorem stage_path (ui e H ρ χ C εentry b₀ : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hH : 0 < H) (hρ : 0 < ρ ∧ ρ < 1)
    (hχ : 0 < χ) (hC : 0 ≤ C) (he : 0 < εentry) (hb : 0 < b₀)
    (σprev : ℕ → ℝ) (n : ℕ) :
    let b := stageRadius ρ b₀ n
    let T := stageDuration H ρ b₀ χ C εentry σprev n
    0 < T ∧ ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
      γ.V T < 0 → ∃ σ ≥ 0,
        σ = ∫ τ in 0..T, ‖deriv (curveParallel e S S.a γ.U γ.V 0) τ‖ ∧
        curveCovVar e S S.a γ.U γ.V 0 T = ENNReal.ofReal σ ∧
        ∃ uNext ∈ Ioo (γ.U T) (γ.V T),
          S.r uNext (γ.V T) = stageRadius ρ b₀ (n + 1) ∧
          (∀ u ∈ Icc (γ.U T) uNext,
            (u, γ.V T) ∈ origDomain ui ∧
            stageRadius ρ b₀ (n + 1) ≤ S.r u (γ.V T) ∧
            S.r u (γ.V T) ≤ b) ∧
          cylinderClock S (fun _ => γ.V T) (γ.U T) uNext = (1 - ρ) * b := by
  dsimp only
  have hT := stageDuration_pos hH hρ.1 hb hχ hC he σprev n
  refine ⟨hT, ?_⟩
  intro γ hproper
  have hp := γ.mem _ (right_mem_Icc.mpr hT.le)
  have hb' := stageRadius_pos hρ.1 hb n
  have hac := Cylinder.ac_curveParallel_a h.solution γ hb' hT.le
  let T := stageDuration H ρ b₀ χ C εentry σprev n
  have huv : γ.U T < γ.V T := by
    by_contra hn
    have heq : γ.U T = γ.V T := le_antisymm hp.2.2.1 (le_of_not_gt hn)
    rw [heq] at hp
    have hz := (h.solution.axis _ hp).1
    have hr := γ.radius _ (right_mem_Icc.mpr hT.le)
    rw [heq, hz] at hr
    exact hb'.ne' hr.symm
  obtain ⟨uNext, hu, hr, hrange, hclock⟩ :=
    exists_connector h hp.1 huv hproper hb' hρ (γ.radius _ (right_mem_Icc.mpr hT.le))
  let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
  have hfin : curveCovVar e S S.a γ.U γ.V 0 T ≠ ⊤ :=
    hac.boundedVariationOn_Icc hT.le
  refine ⟨σ, ENNReal.toReal_nonneg, ?_, ENNReal.ofReal_toReal hfin |>.symm,
    uNext, hu, ?_, ?_, hclock⟩
  · exact hac.toReal_eVariationOn_eq_integral_norm_deriv hT.le
  · simpa only [stageRadius_succ] using hr
  · simpa only [stageRadius_succ] using hrange

/-- [internal] Append an available level graph and its incoming connector
to an actual finite boundary. A clamped sum glues the graphs continuously
and monotonically, including the join. The old prefix and all old cuts are
preserved, so repeated append operations have internal project record's coherent-prefix
shape. This constructs only the available finite portion. Constants: none. -/
theorem appendBoundary_of_levelGraph {ui u₀ u₁ v₀ ρ c u₂ b : ℝ}
    {S : Fields} {vb W : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (huc : u₁ ≤ c) (hcu : c ≤ u₂) (hb : 0 < b)
    (hjoin : W u₁ = vb u₁) (hW : ContDiffOn ℝ 1 W (Icc u₁ c))
    (hWmono : MonotoneOn W (Icc u₁ c))
    (hWmem : ∀ u ∈ Icc u₁ c, (u, W u) ∈ origDomain ui ∧ u < W u)
    (hWr : ∀ u ∈ Icc u₁ c, S.r u (W u) = b)
    (hWrate : ∀ u ∈ Ioo u₁ c, HasDerivAt W (-S.nu u (W u) / S.lam u (W u)) u)
    (hcon : ∀ u ∈ Icc c u₂, ρ * b ≤ S.r u (W c) ∧ S.r u (W c) ≤ b)
    (hu₂ : u₂ < W c) :
    ∃ vb' : ℝ → ℝ, ∃ B' : FiniteBoundary S ui u₀ u₂ v₀ ρ vb' (N + 1),
      (∀ u ∈ Icc u₀ u₁, vb' u = vb u) ∧
      (∀ i : Fin (N + 1), B'.cuts i.castSucc = B.cuts i) ∧
      (∀ i : Fin N, B'.cool i.castSucc = B.cool i ∧ B'.radii i.castSucc = B.radii i) ∧
      B'.cool (Fin.last N) = c ∧ B'.radii (Fin.last N) = b ∧
      (∀ u ∈ Icc u₁ c, vb' u = W u) ∧ (∀ u ∈ Icc c u₂, vb' u = W c) := by
  classical
  have h01 : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  let vb' := fun u => vb (min u u₁) + W (min (max u u₁) c) - W u₁
  have hold (u : ℝ) (hu : u ≤ u₁) : vb' u = vb u := by
    simp only [vb', min_eq_left hu, max_eq_right hu, min_eq_left huc]
    ring
  have hnew (u : ℝ) (hu : u₁ ≤ u) : vb' u = W (min u c) := by
    simp only [vb', min_eq_right hu, max_eq_left hu, hjoin]
    ring
  have hcyl (u : ℝ) (hu : u ∈ Icc u₁ c) : vb' u = W u := by
    rw [hnew u hu.1, min_eq_left hu.2]
  have hconnector (u : ℝ) (hu : u ∈ Icc c u₂) : vb' u = W c := by
    rw [hnew u (huc.trans hu.1), min_eq_right hu.1]
  have hvb : ContinuousOn vb' (Icc u₀ u₂) := by
    have hc₁ : ContinuousOn (fun u => vb (min u u₁)) (Icc u₀ u₂) :=
      B.cont.comp (continuous_id.min continuous_const).continuousOn
      (fun u hu => ⟨le_min hu.1 h01, min_le_right _ _⟩)
    have hc₂ : ContinuousOn (fun u => W (min (max u u₁) c)) (Icc u₀ u₂) := hW.continuousOn.comp
      ((continuous_id.max continuous_const).min continuous_const).continuousOn
      (fun u _ => ⟨le_min (le_max_right _ _) huc, min_le_right _ _⟩)
    exact (hc₁.add hc₂).sub continuousOn_const
  have hvbm : MonotoneOn vb' (Icc u₀ u₂) := by
    intro u hu v hv huv
    have h₁ := B.mono ⟨le_min hu.1 h01, min_le_right _ _⟩
      ⟨le_min hv.1 h01, min_le_right _ _⟩ (min_le_min_right u₁ huv)
    have h₂ := hWmono ⟨le_min (le_max_right _ _) huc, min_le_right _ _⟩
      ⟨le_min (le_max_right _ _) huc, min_le_right _ _⟩
      (min_le_min_right c (max_le_max_right u₁ huv))
    dsimp only [vb']
    linarith only [h₁, h₂]
  have hmem : ∀ u ∈ Icc u₀ u₂, (u, vb' u) ∈ origDomain ui ∧ u < vb' u := by
    intro u hu
    by_cases hu₁ : u ≤ u₁
    · rw [hold u hu₁]
      exact ⟨B.mem u ⟨hu.1, hu₁⟩, B.off_axis u ⟨hu.1, hu₁⟩⟩
    · have h₁ := (lt_of_not_ge hu₁).le
      by_cases huc' : u ≤ c
      · rw [hcyl u ⟨h₁, huc'⟩]
        exact hWmem u ⟨h₁, huc'⟩
      · have hcu' : c ≤ u := (lt_of_not_ge huc').le
        rw [hconnector u ⟨hcu', hu.2⟩]
        have hp := (hWmem c ⟨huc, le_rfl⟩).1
        have hub := hu.2.trans_lt hu₂
        exact ⟨⟨hp.1.trans hcu', hub.trans_le hp.2.2.2, hub.le, hp.2.2.2⟩, hub⟩
  let cuts : Fin (N + 2) → ℝ := Fin.lastCases u₂ B.cuts
  have hcuts : Monotone cuts := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last, B.last]
      exact huc.trans hcu
    · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc] using
        B.ordered (Fin.castSucc_le_succ j)
  let B' : FiniteBoundary S ui u₀ u₂ v₀ ρ vb' (N + 1) :=
    { cuts := cuts
      cool := Fin.lastCases c B.cool
      radii := Fin.lastCases b B.radii
      first := by
        change Fin.lastCases u₂ B.cuts ((0 : Fin (N + 1)).castSucc) = u₀
        simpa only [Fin.lastCases_castSucc] using B.first
      last := by simp only [cuts, Fin.lastCases_last]
      ordered := hcuts
      split := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.succ_last, B.last]
          exact ⟨huc, hcu⟩
        · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc] using B.split j
      entry_label := by rw [hold u₀ h01]; exact B.entry_label
      mem := fun u hu => (hmem u hu).1
      off_axis := fun u hu => (hmem u hu).2
      cont := hvb
      mono := hvbm
      radius_pos := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.lastCases_last] using hb
        · simpa only [Fin.lastCases_castSucc] using B.radius_pos j
      cylinder := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.lastCases_last, B.last]
          intro u hu
          rw [hcyl u hu]
          exact hWr u hu
        · simp only [cuts, Fin.lastCases_castSucc]
          intro u hu
          rw [hold u (hu.2.trans ((B.split j).2.trans (hlast _)))]
          exact B.cylinder j u hu
      cylinder_c1 := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.lastCases_last, B.last]
          exact hW.congr (fun u hu => hcyl u hu)
        · simp only [cuts, Fin.lastCases_castSucc]
          exact (B.cylinder_c1 j).congr (fun u hu =>
            hold u (hu.2.trans ((B.split j).2.trans (hlast _))))
      cylinder_rate := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.lastCases_last, B.last]
          rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo u₁ c =ᵐ[volume] Icc u₁ c)]
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          have he : vb' =ᶠ[nhds u] W := by
            filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
            exact hcyl x ⟨hx.1.le, hx.2.le⟩
          rw [he.deriv_eq, (hWrate u hu).deriv, hcyl u ⟨hu.1.le, hu.2.le⟩]
        · simp only [cuts, Fin.lastCases_castSucc]
          filter_upwards [B.cylinder_rate j, ae_restrict_mem measurableSet_Icc,
            ae_restrict_of_ae ((volume : Measure ℝ).ae_ne u₁)] with u hd hu hne
          have hul : u < u₁ := lt_of_le_of_ne
            (hu.2.trans ((B.split j).2.trans (hlast _))) hne
          have he : vb' =ᶠ[nhds u] vb := by
            filter_upwards [gt_mem_nhds hul] with x hx
            exact hold x hx.le
          rw [he.deriv_eq, hold u hul.le]
          exact hd
      connector := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_last, Fin.succ_last]
          intro u hu
          rw [hconnector u hu, hcyl c ⟨huc, le_rfl⟩]
        · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc]
          intro u hu
          rw [hold u (hu.2.trans (hlast _)),
            hold (B.cool j) ((B.split j).2.trans (hlast _))]
          exact B.connector j u hu
      radius_range := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.succ_last, B.last]
          intro u hu
          by_cases huc' : u ≤ c
          · rw [hcyl u ⟨hu.1, huc'⟩, hWr u ⟨hu.1, huc'⟩]
            have hp := hcon c ⟨le_rfl, hcu⟩
            rw [hWr c ⟨huc, le_rfl⟩] at hp
            exact ⟨hp.1, le_rfl⟩
          · have hh : u ∈ Icc c u₂ := ⟨(lt_of_not_ge huc').le, hu.2⟩
            rw [hconnector u hh]
            exact hcon u hh
        · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc]
          intro u hu
          rw [hold u (hu.2.trans (hlast _))]
          exact B.radius_range j u hu }
  refine ⟨vb', B', (fun u hu => hold u hu.2), ?_, ?_, ?_, ?_, hcyl, hconnector⟩ <;>
    simp [B', cuts]

/-- [internal] Transfer an actual finite path to a graph agreeing on its
prefix. This converts coherent finite append constructions to internal project record's
single global graph without assuming stage existence. The cuts, cooling
endpoints and radii are preserved definitionally. Derivatives agree a.e.;
no regularity outside the visited prefix is required. Constants: none. -/
@[expose] def transportBoundary {S : Fields} {ui u₀ u₁ v₀ ρ : ℝ} {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (vb' : ℝ → ℝ)
    (heq : EqOn vb' vb (Icc u₀ u₁)) : FiniteBoundary S ui u₀ u₁ v₀ ρ vb' N := by
  have hfirst (i : Fin (N + 1)) : u₀ ≤ B.cuts i := B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ u₁ := (B.ordered (Fin.le_last i)).trans B.last.le
  have h01 : u₀ ≤ u₁ := by simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hstage (n : Fin N) : Icc (B.cuts n.castSucc) (B.cuts n.succ) ⊆ Icc u₀ u₁ :=
    Icc_subset_Icc (hfirst _) (hlast _)
  have hcool (n : Fin N) : B.cool n ∈ Icc u₀ u₁ :=
    ⟨(hfirst _).trans (B.split n).1, (B.split n).2.trans (hlast _)⟩
  exact
    { cuts := B.cuts, cool := B.cool, radii := B.radii, first := B.first, last := B.last
      ordered := B.ordered, split := B.split
      entry_label := by rw [heq ⟨le_rfl, h01⟩]; exact B.entry_label
      mem := fun u hu => by rw [heq hu]; exact B.mem u hu
      off_axis := fun u hu => by rw [heq hu]; exact B.off_axis u hu
      cont := B.cont.congr heq
      mono := by intro u hu v hv huv; rw [heq hu, heq hv]; exact B.mono hu hv huv
      radius_pos := B.radius_pos
      cylinder := by
        intro n u hu
        rw [heq (hstage n ⟨hu.1, hu.2.trans (B.split n).2⟩)]
        exact B.cylinder n u hu
      cylinder_c1 := fun n => (B.cylinder_c1 n).congr
        (fun u hu => heq (hstage n ⟨hu.1, hu.2.trans (B.split n).2⟩))
      cylinder_rate := by
        intro n
        filter_upwards [B.cylinder_rate n, ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae ((volume : Measure ℝ).ae_ne u₀),
          ae_restrict_of_ae ((volume : Measure ℝ).ae_ne u₁)] with u hd hu hn₀ hn₁
        have hp := hstage n ⟨hu.1, hu.2.trans (B.split n).2⟩
        have hl : u₀ < u := lt_of_le_of_ne hp.1 hn₀.symm
        have hr : u < u₁ := lt_of_le_of_ne hp.2 hn₁
        have hh : vb' =ᶠ[nhds u] vb := by
          filter_upwards [Ioo_mem_nhds hl hr] with x hx
          exact heq ⟨hx.1.le, hx.2.le⟩
        rw [hh.deriv_eq, heq hp]
        exact hd
      connector := by
        intro n u hu
        rw [heq (hstage n ⟨(B.split n).1.trans hu.1, hu.2⟩), heq (hcool n)]
        exact B.connector n u hu
      radius_range := fun n u hu => by rw [heq (hstage n hu)]; exact B.radius_range n u hu }

end EmcsfAcExtension.Global.Closure
