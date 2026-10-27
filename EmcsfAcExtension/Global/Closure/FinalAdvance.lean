module

public import EmcsfAcExtension.Global.Closure.FinalFamilies
import EmcsfAcExtension.Global.Observation.CylinderClock
import Mathlib.Tactic

/-! # One completed cylinder and connector stage

The geometric append keeps its capped duration until strict stopping
excludes the terminal row. Only then is the duration identified with the
prescribed clock. The connector is capped and completed in the same way.
Source: `charged_SF_new_version.tex:L3899–L3917`, `charged_SF_new_version.tex:L4104–L4115`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Complete one actual cylinder and connector, preserving the whole old
history. The stopped-path input of this helper is the explicit consumer of
the numerical cutoff callback and actual finite stopping continuation.
It is used twice, on the capped cylinder and capped connector; it assumes
neither that a stage exists nor that a cap reaches its prescribed target.
No node or final theorem is claimed by this conditional helper. All
parameters and the stopped-path consumer precede the stage index. -/
theorem final_prefix_extension_of_stopped_paths {S : Fields}
    {ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun : ℝ}
    (h : OriginalData ui e S) (hia : ui < a) (hρ : 0 < ρ ∧ ρ < 1)
    (hb₀ : 0 < b₀) (hbsmall : b₀ < R₀ / 2)
    (hH : 0 < H) (hχ : 0 < χ) (hC₁ : 0 ≤ C₁) (he : 0 < εentry)
    (hpaths : ∀ (b : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ) (N : ℕ)
      (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ),
      (∀ n, 0 < T n) →
      (∀ n : Fin N, B.radii n = stageRadius ρ b₀ n) →
      (∀ n : Fin N, T n ≤ H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      (∀ n : Fin N, n.val + 1 < N →
        T n = H * B.radii n / energyEnvelope χ C₁ εentry σ n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      StrictFiniteCutoffStops S ui a R₀ vb
        (fun _ => (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal)
        (fun _ => ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal)
        δ c Λ F εweak εrun b)
    (N : ℕ) (P : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun N) :
    ∃ Q : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun (N + 1),
      P.endpoint < Q.endpoint ∧
      EqOn Q.graph P.graph (Icc a P.endpoint) ∧
      (∀ i : Fin (N + 1), Q.boundary.cuts i.castSucc = P.boundary.cuts i) ∧
      (∀ i : Fin N, Q.boundary.cool i.castSucc = P.boundary.cool i ∧
        Q.boundary.radii i.castSucc = P.boundary.radii i) ∧
      (∀ k < N, Q.variation k = P.variation k) ∧
      ∀ i : Fin N, Q.duration i.castSucc = P.duration i ∧
        (Q.cylinders i.castSucc).U = (P.cylinders i).U ∧
        (Q.cylinders i.castSucc).V = (P.cylinders i).V := by
  have hac : a ≤ P.endpoint := by
    simpa only [P.boundary.first, P.boundary.last] using
      P.boundary.ordered (Fin.zero_le (Fin.last N))
  have hRpos : 0 < stageRadius ρ b₀ N := mul_pos (pow_pos hρ.1 N) hb₀
  have hRsmall : stageRadius ρ b₀ N < R₀ / 2 := by
    apply lt_of_le_of_lt _ hbsmall
    exact mul_le_of_le_one_left hb₀.le (pow_le_one₀ hρ.1.le hρ.2.le)
  have hterminal : R₀ / 2 < S.r P.endpoint 0 := P.stops.2.2.1 _ ⟨hac, le_rfl⟩
  have hv : P.graph P.endpoint < 0 := by
    have hv0 := (P.boundary.mem P.endpoint ⟨hac, le_rfl⟩).2.2.2
    change P.graph P.endpoint ≤ 0 at hv0
    apply lt_of_le_of_ne hv0
    intro hvzero
    have hr := P.endpoint_radius
    rw [hvzero] at hr
    linarith only [hr, hterminal, hRsmall]
  let R := stageRadius ρ b₀ N
  let Tmax := H * R / energyEnvelope χ C₁ εentry P.variation N
  have hTmax : 0 < Tmax := div_pos (mul_pos hH hRpos) (energyEnvelope_pos hχ hC₁ he _ _)
  obtain ⟨W, bcap, hbcap, t, ht, htmax, γlast, vbC, BC, hU, hV, holdC, hcutsC,
    hstagesC, hcoolC, hradiusC, hW, hgraphlast, hretainedC, hbcapR, haltC⟩ :=
    capped_boundary_append h P.boundary (hia.trans_le hac) hρ hRpos hRsmall
      P.endpoint_radius hterminal hv hTmax
  obtain ⟨TC, γC, hTC, hendsC, hgraphC, hprevC, hlastC⟩ :=
    append_clock_family h P.boundary BC P.duration P.duration_pos P.cylinders P.ends
      P.on_graph holdC hcutsC hstagesC ht γlast hU hcoolC hradiusC hgraphlast
  let σlast := (curveCovVar e S S.a γlast.U γlast.V 0 t).toReal
  let σ := Function.update P.variation N σlast
  have hbefore (k : ℕ) (hk : k < N) : σ k = P.variation k :=
    Function.update_of_ne (by omega) _ _
  have henv (k : ℕ) (hk : k ≤ N) : energyEnvelope χ C₁ εentry σ k =
      energyEnvelope χ C₁ εentry P.variation k := by
    apply energyEnvelope_congr_before
    intro j hj
    exact hbefore j (hj.trans_le hk)
  have hσC (i : Fin (N + 1)) : σ i =
      (curveCovVar e S S.a (γC i).U (γC i).V 0 (TC i)).toReal := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hlastC.2.1, hlastC.2.2, hlastC.1]
      simp only [Fin.val_last]
      exact Function.update_self _ _ _
    · simp only [Fin.val_castSucc]
      rw [hbefore j j.isLt, (hprevC j).2.1, (hprevC j).2.2, (hprevC j).1]
      exact P.variation_eq j
  have hradiiC (i : Fin (N + 1)) : BC.radii i = stageRadius ρ b₀ i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact hradiusC
    · exact (hstagesC j).2.trans (P.radii_eq j)
  have hpriorC (i : Fin (N + 1)) (hi : i.val + 1 < N + 1) :
      TC i = H * BC.radii i / energyEnvelope χ C₁ εentry σ i := by
    let j : Fin N := ⟨i.val, by omega⟩
    have hij : i = j.castSucc := rfl
    rw [hij, (hprevC j).1, (hstagesC j).2]
    simp only [Fin.val_castSucc]
    rw [henv j (by have hj := j.isLt; omega)]
    exact P.duration_eq j
  have hshortC (i : Fin (N + 1)) :
      TC i ≤ H * BC.radii i / energyEnvelope χ C₁ εentry σ i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hlastC.1, hradiusC]
      simp only [Fin.val_last]
      rw [henv N le_rfl]
      exact htmax
    · exact (hpriorC j.castSucc (by have hj := j.isLt; simp only [Fin.val_castSucc]; omega)).le
  have hstopC := hpaths _ vbC σ (N + 1) BC TC hTC hradiiC hshortC hpriorC γC hendsC hgraphC hσC
  have haC : a ≤ γlast.U t := by
    simpa only [BC.first, BC.last] using BC.ordered (Fin.zero_le (Fin.last (N + 1)))
  have htfull : t = Tmax := prescribed_clock_of_strict_cutoff haC hstopC hbcapR haltC
  have hscheduledC (i : Fin (N + 1)) :
      TC i = H * BC.radii i / energyEnvelope χ C₁ εentry σ i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [hlastC.1, hradiusC]
      simp only [Fin.val_last]
      rw [henv N le_rfl]
      exact htfull
    · exact hpriorC j.castSucc (by have hj := j.isLt; simp only [Fin.val_castSucc]; omega)
  have hterminalC : R₀ / 2 < S.r (γlast.U t) 0 := hstopC.2.2.1 _ ⟨haC, le_rfl⟩
  have hvC : vbC (γlast.U t) < 0 := by
    have hv0 := (BC.mem (γlast.U t) ⟨haC, le_rfl⟩).2.2.2
    change vbC (γlast.U t) ≤ 0 at hv0
    apply lt_of_le_of_ne hv0
    intro hvzero
    have hr := BC.cylinder (Fin.last N) (γlast.U t)
      ⟨(BC.split _).1.trans_eq hcoolC, hcoolC.ge⟩
    rw [hvzero, hradiusC] at hr
    linarith only [hr, hterminalC, hRsmall]
  obtain ⟨btarget, hbtarget, hbtargetR, d, hd, vbD, BD, holdD, hcutsD,
    hstagesD, hconD, hretainedD, haltD, hclockD, hclockDle⟩ :=
    capped_last_connector h BC hcoolC hρ hvC hterminalC
  obtain ⟨γD, hcurvesD, hendsD, hgraphD⟩ := connector_clock_family h BC BD TC hTC γC
    hendsC hgraphC holdD hcutsD hstagesD
  have hradiiD (i : Fin (N + 1)) : BD.radii i = stageRadius ρ b₀ i :=
    (hstagesD i).2.trans (hradiiC i)
  have hscheduledD (i : Fin (N + 1)) :
      TC i = H * BD.radii i / energyEnvelope χ C₁ εentry σ i := by
    rw [(hstagesD i).2]
    exact hscheduledC i
  have hσD (i : Fin (N + 1)) : σ i =
      (curveCovVar e S S.a (γD i).U (γD i).V 0 (TC i)).toReal := by
    rw [(hcurvesD i).1, (hcurvesD i).2]
    exact hσC i
  have hstopD := hpaths d vbD σ (N + 1) BD TC hTC hradiiD
    (fun i => (hscheduledD i).le) (fun i _ => hscheduledD i) γD hendsD hgraphD hσD
  have haD : a ≤ d := haC.trans hd.1.le
  have hdtarget : d = btarget := connector_target_of_strict_cutoff haD hstopD haltD
  have hfinalR : S.r d (vbD d) = stageRadius ρ b₀ (N + 1) := by
    rw [hconD d ⟨hd.1.le, le_rfl⟩, hdtarget, hbtargetR, hradiusC, stageRadius_succ]
  have hzero (k : ℕ) (hk : N + 1 ≤ k) : σ k = 0 := by
    change Function.update P.variation N σlast k = 0
    rw [Function.update_of_ne (show k ≠ N by omega)]
    exact P.variation_zero k (by omega)
  let Q : FinalPrefix S ui e a v₀ ρ b₀ H χ C₁ εentry R₀ δ c Λ F εweak εrun (N + 1) :=
    { endpoint := d, graph := vbD, boundary := BD, variation := σ,
      variation_zero := hzero, duration := TC, duration_pos := hTC,
      cylinders := γD, ends := hendsD, on_graph := hgraphD, variation_eq := hσD,
      radii_eq := hradiiD, duration_eq := hscheduledD,
      endpoint_radius := hfinalR, stops := hstopD }
  have hc : P.endpoint < γlast.U t := by
    simpa only [hU] using γlast.strictMonoOn_U h.solution ⟨le_rfl, ht.le⟩
      ⟨ht.le, le_rfl⟩ ht
  refine ⟨Q, hc.trans hd.1, ?_, ?_, ?_, hbefore, ?_⟩
  · intro u hu
    exact (holdD u ⟨hu.1, hu.2.trans hc.le⟩).trans (holdC u hu)
  · intro i
    exact (hcutsD i).trans (hcutsC i)
  · intro i
    exact ⟨(hstagesD i.castSucc).1.trans (hstagesC i).1,
      (hstagesD i.castSucc).2.trans (hstagesC i).2⟩
  · intro i
    exact ⟨(hprevC i).1, (hcurvesD i.castSucc).1.trans (hprevC i).2.1,
      (hcurvesD i.castSucc).2.trans (hprevC i).2.2⟩

end EmcsfAcExtension.Global.Closure
