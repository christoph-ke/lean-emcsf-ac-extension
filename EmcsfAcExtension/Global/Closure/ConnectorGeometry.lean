module

public import EmcsfAcExtension.Global.Closure.Stages
public import EmcsfAcExtension.Global.Closure.Clock
public import EmcsfAcExtension.Global.Closure.Continuation
import Mathlib.Tactic

/-! # Appending the actual constant-label connector

Extend the degenerate last connector returned by `capped_boundary_append`
without adding a stage or changing any completed cylinder. The new incoming
segment is capped at its target radius or the proper terminal stopping row.
Source: `charged_SF_new_version.tex:L3905–L3917`, `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Extend only the last, degenerate connector of a finite boundary along its
constant incoming label. Every earlier cut and every cylinder endpoint and
radius is preserved. The last cut becomes the supplied proper connector
endpoint. No field estimate or new structure is used. Constants: none. -/
theorem extend_last_connector {S : Fields} {ui u₀ c d v₀ ρ : ℝ}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ c v₀ ρ vb (N + 1))
    (hcool : B.cool (Fin.last N) = c) (hcd : c ≤ d) (hdv : d < vb c)
    (hrange : ∀ u ∈ Icc c d,
      ρ * B.radii (Fin.last N) ≤ S.r u (vb c) ∧ S.r u (vb c) ≤ B.radii (Fin.last N)) :
    ∃ vb' : ℝ → ℝ, ∃ B' : FiniteBoundary S ui u₀ d v₀ ρ vb' (N + 1),
      (∀ u ∈ Icc u₀ c, vb' u = vb u) ∧
      (∀ i : Fin (N + 1), B'.cuts i.castSucc = B.cuts i.castSucc) ∧
      (∀ i : Fin (N + 1), B'.cool i = B.cool i ∧ B'.radii i = B.radii i) ∧
      (∀ u ∈ Icc c d, vb' u = vb c) := by
  classical
  have hfirst (i : Fin (N + 2)) : u₀ ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 2)) : B.cuts i ≤ c :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have h0c : u₀ ≤ c := (hfirst (Fin.last (N + 1))).trans B.last.le
  have hcool_le (i : Fin (N + 1)) : B.cool i ≤ c := (B.split i).2.trans (hlast _)
  let vb' := fun u => vb (min u c)
  have hold (u : ℝ) (hu : u ≤ c) : vb' u = vb u := by
    simp only [vb', min_eq_left hu]
  have hcon (u : ℝ) (hu : c ≤ u) : vb' u = vb c := by
    simp only [vb', min_eq_right hu]
  let cuts : Fin (N + 2) → ℝ := Fin.lastCases d (fun i => B.cuts i.castSucc)
  have hcuts : Monotone cuts := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last]
      exact (hlast _).trans hcd
    · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc] using
        B.ordered (Fin.castSucc_le_succ j.castSucc)
  have hclamp (u : ℝ) (hu : u ∈ Icc u₀ d) : min u c ∈ Icc u₀ c :=
    ⟨le_min hu.1 h0c, min_le_right _ _⟩
  have hmem (u : ℝ) (hu : u ∈ Icc u₀ d) :
      (u, vb' u) ∈ origDomain ui ∧ u < vb' u := by
    by_cases huc : u ≤ c
    · rw [hold u huc]
      exact ⟨B.mem u ⟨hu.1, huc⟩, B.off_axis u ⟨hu.1, huc⟩⟩
    · have hcu : c ≤ u := (lt_of_not_ge huc).le
      rw [hcon u hcu]
      have hp := B.mem c ⟨h0c, le_rfl⟩
      have huv := hu.2.trans_lt hdv
      exact ⟨⟨hp.1.trans hcu, huv.trans_le hp.2.2.2, huv.le, hp.2.2.2⟩, huv⟩
  let B' : FiniteBoundary S ui u₀ d v₀ ρ vb' (N + 1) :=
    { cuts := cuts
      cool := B.cool
      radii := B.radii
      first := by
        change Fin.lastCases d (fun i : Fin (N + 1) => B.cuts i.castSucc)
          ((0 : Fin (N + 1)).castSucc) = u₀
        rw [Fin.lastCases_castSucc, Fin.castSucc_zero]
        exact B.first
      last := by simp only [cuts, Fin.lastCases_last]
      ordered := hcuts
      split := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last, hcool]
          exact ⟨(B.split (Fin.last N)).1.trans_eq hcool, hcd⟩
        · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc] using B.split j.castSucc
      entry_label := by rw [hold u₀ h0c]; exact B.entry_label
      mem := fun u hu => (hmem u hu).1
      off_axis := fun u hu => (hmem u hu).2
      cont := B.cont.comp (continuous_id.min continuous_const).continuousOn hclamp
      mono := fun _ hu _ hv huv => B.mono (hclamp _ hu) (hclamp _ hv) (min_le_min_right c huv)
      radius_pos := B.radius_pos
      cylinder := by
        intro n u hu
        have hu' : u ∈ Icc (B.cuts n.castSucc) (B.cool n) := by
          simpa only [cuts, Fin.lastCases_castSucc] using hu
        rw [hold u (hu'.2.trans (hcool_le n))]
        exact B.cylinder n u hu'
      cylinder_c1 := by
        intro n
        simp only [cuts, Fin.lastCases_castSucc]
        exact (B.cylinder_c1 n).congr (fun u hu => hold u (hu.2.trans (hcool_le n)))
      cylinder_rate := by
        intro n
        simp only [cuts, Fin.lastCases_castSucc]
        filter_upwards [B.cylinder_rate n, ae_restrict_mem measurableSet_Icc,
          ae_restrict_of_ae ((volume : Measure ℝ).ae_ne c)] with u hd hu hne
        have huc : u < c := lt_of_le_of_ne (hu.2.trans (hcool_le n)) hne
        have heq : vb' =ᶠ[𝓝 u] vb := by
          filter_upwards [gt_mem_nhds huc] with x hx
          exact hold x hx.le
        rw [heq.deriv_eq, hold u huc.le]
        exact hd
      connector := by
        intro n
        refine Fin.lastCases ?_ (fun j => ?_) n
        · simp only [cuts, Fin.succ_last, Fin.lastCases_last, hcool]
          intro u hu
          rw [hcon u hu.1, hold c le_rfl]
        · simp only [cuts, Fin.succ_castSucc, Fin.lastCases_castSucc]
          intro u hu
          rw [hold u (hu.2.trans (hlast _)), hold _ (hcool_le _)]
          exact B.connector j.castSucc u hu
      radius_range := by
        intro n
        refine Fin.lastCases ?_ (fun j => ?_) n
        · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last]
          intro u hu
          by_cases huc : u ≤ c
          · rw [hold u huc]
            exact B.radius_range (Fin.last N) u
              ⟨hu.1, by simpa only [Fin.succ_last, B.last] using huc⟩
          · rw [hcon u (lt_of_not_ge huc).le]
            exact hrange u ⟨(lt_of_not_ge huc).le, hu.2⟩
        · simp only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc]
          intro u hu
          rw [hold u (hu.2.trans (hlast _))]
          exact B.radius_range j.castSucc u hu }
  exact ⟨vb', B', (fun u hu => hold u hu.2),
    (by intro i; simp only [B', cuts, Fin.lastCases_castSucc]),
    (fun _ => ⟨rfl, rfl⟩), (fun u hu => hcon u hu.1)⟩

/-- [internal]
Construct the actual constant-label connector after a completed cylinder,
capped by its next radius or the proper terminal stopping row. It extends
the exact finite record from `capped_boundary_append`, preserving all old
cuts and cylinder data. Its clock is the radius loss and is bounded by the
full geometric drop. Constants: one, uniform in every scale and stage.
The strict-stop and radius-estimate consumers in `ConnectorExclusion`
exclude the terminal-row alternative. -/
theorem capped_last_connector {ui e u₀ c v₀ ρ Rmin : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ c v₀ ρ vb (N + 1))
    (hcool : B.cool (Fin.last N) = c) (hρ : 0 < ρ ∧ ρ < 1)
    (hv : vb c < 0) (hterminal : Rmin < S.r c 0) :
    ∃ b ∈ Ioo c (vb c), S.r b (vb c) = ρ * B.radii (Fin.last N) ∧
      ∃ d ∈ Ioc c b, ∃ vb' : ℝ → ℝ,
      ∃ B' : FiniteBoundary S ui u₀ d v₀ ρ vb' (N + 1),
        (∀ u ∈ Icc u₀ c, vb' u = vb u) ∧
        (∀ i : Fin (N + 1), B'.cuts i.castSucc = B.cuts i.castSucc) ∧
        (∀ i : Fin (N + 1), B'.cool i = B.cool i ∧ B'.radii i = B.radii i) ∧
        (∀ u ∈ Icc c d, vb' u = vb c) ∧
        (∀ u ∈ Icc c d, Rmin ≤ S.r u 0) ∧
        (d = b ∨ S.r d 0 = Rmin) ∧
        cylinderClock S vb' c d = B.radii (Fin.last N) - S.r d (vb c) ∧
        cylinderClock S vb' c d ≤ (1 - ρ) * B.radii (Fin.last N) := by
  have h0c : u₀ ≤ c := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last (N + 1)))
  have hp := B.mem c ⟨h0c, le_rfl⟩
  have hstart : S.r c (vb c) = B.radii (Fin.last N) :=
    B.cylinder (Fin.last N) c ⟨(B.split _).1.trans_eq hcool, hcool.ge⟩
  obtain ⟨b, hb, hbr, hsegment, _⟩ := exists_connector h hp.1
    (B.off_axis c ⟨h0c, le_rfl⟩) hv (B.radius_pos _) hρ hstart
  obtain ⟨d, hd, hretained, halt⟩ := terminal_radius_cap h hp.1 hb.1 (hb.2.trans hv) hterminal
  have hdv : d < vb c := hd.2.trans_lt hb.2
  obtain ⟨vb', B', hold, hcuts, hstages, hcon⟩ := extend_last_connector B hcool hd.1.le hdv
    (fun u hu => (hsegment u ⟨hu.1, hu.2.trans hd.2⟩).2)
  have hclock : cylinderClock S vb' c d = B.radii (Fin.last N) - S.r d (vb c) := by
    have heq : cylinderClock S vb' c d = cylinderClock S (fun _ => vb c) c d := by
      apply intervalIntegral.integral_congr
      intro u hu
      change -S.nu u (vb' u) = -S.nu u (vb c)
      rw [hcon u (by simpa only [uIcc_of_le hd.1.le] using hu)]
    rw [heq, connector_clock_eq_radius_loss h.solution hd.1.le hdv.le, hstart]
    rintro ⟨u, v⟩ ⟨hu, hud, rfl⟩
    exact (hsegment u ⟨hu, hud.trans hd.2⟩).1
  refine ⟨b, hb, hbr, d, hd, vb', B', hold, hcuts, hstages, hcon, hretained, halt, hclock, ?_⟩
  rw [hclock]
  have hr := (hsegment d ⟨hd.1.le, hd.2⟩).2.1
  linarith only [hr]

end EmcsfAcExtension.Global.Closure
