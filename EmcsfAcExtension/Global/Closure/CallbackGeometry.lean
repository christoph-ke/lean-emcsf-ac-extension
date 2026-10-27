module

public import EmcsfAcExtension.Global.Closure.Stages
import Mathlib.Tactic

/-! # Finite records for the cutoff callback

Take the completed part of an available boundary and cut its last stage at
an arbitrary physical point. The graph itself is retained, so the incoming
norm on the restricted exterior is the literal cutoff norm.
Source: `charged_SF_new_version.tex:L3919–L3929`, `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The first `M` stages of an available finite boundary, on the same graph.
Every cut, cooling endpoint and radius is inherited. Constants: none. -/
@[expose] def takeBoundary {S : Fields} {ui a b v₀ ρ : ℝ} {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (M : ℕ) (hMN : M ≤ N) :
    FiniteBoundary S ui a (B.cuts ⟨M, by omega⟩) v₀ ρ vb M := by
  let f : Fin (M + 1) → Fin (N + 1) := Fin.castLE (by omega)
  let g : Fin M → Fin N := Fin.castLE hMN
  have hfg (n : Fin M) : f n.castSucc = (g n).castSucc := rfl
  have hfs (n : Fin M) : f n.succ = (g n).succ := rfl
  have hsub : Icc a (B.cuts ⟨M, by omega⟩) ⊆ Icc a b := by
    apply Icc_subset_Icc le_rfl
    exact (B.ordered (Fin.le_last _)).trans B.last.le
  exact
    { cuts := fun i => B.cuts (f i)
      cool := fun n => B.cool (g n)
      radii := fun n => B.radii (g n)
      first := B.first
      last := rfl
      ordered := fun _ _ hij => B.ordered hij
      split := fun n => by simpa only [hfg, hfs] using B.split (g n)
      entry_label := B.entry_label
      mem := fun u hu => B.mem u (hsub hu)
      off_axis := fun u hu => B.off_axis u (hsub hu)
      cont := B.cont.mono hsub
      mono := B.mono.mono hsub
      radius_pos := fun n => B.radius_pos (g n)
      cylinder := fun n => B.cylinder (g n)
      cylinder_c1 := fun n => B.cylinder_c1 (g n)
      cylinder_rate := fun n => B.cylinder_rate (g n)
      connector := fun n => B.connector (g n)
      radius_range := fun n => B.radius_range (g n) }

/-- [internal]
Cut the last available stage at `x`. Its cooling endpoint becomes the
minimum of the old endpoint and `x`; the last connector is a singleton
when the cutoff is inside the cylinder. Earlier stages and the boundary
graph are unchanged. Constants: none. -/
@[expose] def cutLastBoundary {S : Fields} {ui a b v₀ ρ : ℝ} {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb (N + 1)) (x : ℝ)
    (hx : x ∈ Icc (B.cuts (Fin.last N).castSucc) b) :
    FiniteBoundary S ui a x v₀ ρ vb (N + 1) := by
  let cuts : Fin (N + 2) → ℝ := Fin.lastCases x (fun i => B.cuts i.castSucc)
  let cool : Fin (N + 1) → ℝ :=
    Fin.lastCases (min (B.cool (Fin.last N)) x) (fun i => B.cool i.castSucc)
  have hfirst (i : Fin (N + 2)) : a ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 2)) : B.cuts i ≤ b :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hcuts : Monotone cuts := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_last,
        Fin.lastCases_last] using hx.1
    · simpa only [cuts, Fin.lastCases_castSucc, Fin.succ_castSucc] using
        B.ordered (Fin.castSucc_le_succ j.castSucc)
  have hcool (n : Fin (N + 1)) : cool n ≤ B.cool n := by
    refine Fin.lastCases ?_ (fun j => ?_) n
    · simp only [cool, Fin.lastCases_last]
      exact min_le_left _ _
    · simp only [cool, Fin.lastCases_castSucc, le_refl]
  have hcyl (n : Fin (N + 1)) :
      Icc (cuts n.castSucc) (cool n) ⊆ Icc (B.cuts n.castSucc) (B.cool n) := by
    simp only [cuts, Fin.lastCases_castSucc]
    exact Icc_subset_Icc le_rfl (hcool n)
  exact
    { cuts := cuts
      cool := cool
      radii := B.radii
      first := by
        change Fin.lastCases x (fun i : Fin (N + 1) => B.cuts i.castSucc)
          ((0 : Fin (N + 1)).castSucc) = a
        rw [Fin.lastCases_castSucc, Fin.castSucc_zero]
        exact B.first
      last := by simp only [cuts, Fin.lastCases_last]
      ordered := hcuts
      split := by
        intro n
        refine Fin.lastCases ?_ (fun j => ?_) n
        · simp only [cuts, cool, Fin.lastCases_castSucc, Fin.lastCases_last,
            Fin.succ_last]
          exact ⟨le_min (B.split _).1 hx.1, min_le_right _ _⟩
        · simpa only [cuts, cool, Fin.lastCases_castSucc, Fin.succ_castSucc] using
            B.split j.castSucc
      entry_label := B.entry_label
      mem := fun u hu => B.mem u (hsub hu)
      off_axis := fun u hu => B.off_axis u (hsub hu)
      cont := B.cont.mono hsub
      mono := B.mono.mono hsub
      radius_pos := B.radius_pos
      cylinder := fun n u hu => B.cylinder n u (hcyl n hu)
      cylinder_c1 := fun n => (B.cylinder_c1 n).mono (hcyl n)
      cylinder_rate := fun n => (B.cylinder_rate n).filter_mono
        (ae_mono (Measure.restrict_mono (hcyl n) le_rfl))
      connector := by
        intro n
        refine Fin.lastCases ?_ (fun j => ?_) n
        · simp only [cuts, cool, Fin.succ_last, Fin.lastCases_last]
          intro u hu
          by_cases hcx : B.cool (Fin.last N) ≤ x
          · rw [min_eq_left hcx] at hu ⊢
            exact B.connector (Fin.last N) u
              ⟨hu.1, by simpa only [Fin.succ_last, B.last] using hu.2.trans hx.2⟩
          · rw [min_eq_right (le_of_not_ge hcx)] at hu ⊢
            exact congrArg vb (le_antisymm hu.2 hu.1)
        · simpa only [cuts, cool, Fin.succ_castSucc, Fin.lastCases_castSucc] using
            B.connector j.castSucc
      radius_range := by
        intro n
        refine Fin.lastCases ?_ (fun j => ?_) n
        · simp only [cuts, Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc]
          intro u hu
          exact B.radius_range (Fin.last N) u
            ⟨hu.1, by simpa only [Fin.succ_last, B.last] using hu.2.trans hx.2⟩
        · simpa only [cuts, Fin.succ_castSucc, Fin.lastCases_castSucc] using
            B.radius_range j.castSucc }

end EmcsfAcExtension.Global.Closure
