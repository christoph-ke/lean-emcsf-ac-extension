module

public import EmcsfAcExtension.Global.Closure.CallbackGeometry
public import EmcsfAcExtension.Global.Closure.ConnectorClock
import Mathlib.Tactic

/-! # Literal variations on restricted finite histories

Cylinders starting after the cutoff contribute zero to the clipped sum.
Consequently taking the visited finite history preserves the literal
variation used in finite stopping continuation.
Source: `charged_SF_new_version.tex:L3919–L3929`, `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
A cylinder not yet entered contributes zero to the literal clipped
variation. This includes its starting point. Constants: none. -/
theorem clipped_variation_eq_zero_before_start {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (n : Fin N) {x : ℝ} (hx : x ∈ Icc a b) (hxn : x ≤ B.cuts n.castSucc) :
    (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)))).toReal = 0 := by
  have hn : B.cuts n.castSucc ∈ Icc a b :=
    ⟨B.first.ge.trans (B.ordered (Fin.zero_le _)),
      (B.ordered (Fin.le_last _)).trans B.last.le⟩
  have hc := monotoneOn_cylinderClock h B hn hx hn hxn
  simp only [cylinderClock, intervalIntegral.integral_same] at hc
  have hzero : max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)) = 0 :=
    max_eq_left ((min_le_right _ _).trans hc)
  rw [hzero, curveCovVar, Icc_self,
    eVariationOn.subsingleton _ (subsingleton_singleton), ENNReal.toReal_zero]

/-- [internal]
The actual clipped variation at entry is zero on every available finite
history, independently of the number of cylinders. Constants: none. -/
theorem clipped_variation_initial {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n)) :
    (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) a)))).toReal) = 0 := by
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  apply Finset.sum_eq_zero
  intro n _
  exact clipped_variation_eq_zero_before_start h B T γ n ⟨le_rfl, hab⟩
    (B.first.ge.trans (B.ordered (Fin.zero_le _)))

/-- [internal]
Taking the first `M` stages preserves the actual clipped variation at any
cutoff before cut `M`. Every omitted cylinder is still unentered. The
same physical clock functions and graph are used. Constants: none. -/
theorem cutoff_variation_take {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (M : ℕ) (hMN : M ≤ N) {x : ℝ} (hx : x ∈ Icc a b)
    (hxm : x ≤ B.cuts ⟨M, by omega⟩) :
    (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) x)))).toReal) =
    ∑ n : Fin M, (curveCovVar e S S.a (γ (n.castLE hMN)).U
      (γ (n.castLE hMN)).V 0
      (max 0 (min (T (n.castLE hMN))
        (cylinderClock S vb (B.cuts (n.castLE hMN).castSucc) x)))).toReal := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hMN
  rw [Fin.sum_univ_add]
  have hz : (∑ n : Fin K, (curveCovVar e S S.a (γ (n.natAdd M)).U
      (γ (n.natAdd M)).V 0
      (max 0 (min (T (n.natAdd M))
        (cylinderClock S vb (B.cuts (n.natAdd M).castSucc) x)))).toReal) = 0 := by
    apply Finset.sum_eq_zero
    intro n _
    apply clipped_variation_eq_zero_before_start h B T γ _ hx
    exact hxm.trans (B.ordered (by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_castSucc, Fin.val_natAdd]
      omega))
  rw [hz, add_zero]
  rfl

/-- [internal]
Every point strictly after entry and before the final cut belongs to a
stage with strictly earlier starting cut. This avoids a zero-duration
partial cylinder in the strict-improvement consumer. Constants: none. -/
theorem exists_stage_at_cutoff {S : Fields} {ui a b v₀ ρ : ℝ} {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ n : Fin N, B.cuts n.castSucc < x ∧ x ≤ B.cuts n.succ := by
  classical
  have hex : ∃ k : ℕ, ∃ hk : k ≤ N, x ≤ B.cuts ⟨k, by omega⟩ := by
    refine ⟨N, le_rfl, ?_⟩
    change x ≤ B.cuts (Fin.last N)
    rw [B.last]
    exact hx.2
  obtain ⟨hkN, hxk⟩ := Nat.find_spec hex
  have hk0 : 0 < Nat.find hex := by
    by_contra hn
    have heq : Nat.find hex = 0 := by omega
    have hzero : (⟨Nat.find hex, by omega⟩ : Fin (N + 1)) = 0 := Fin.ext heq
    rw [hzero, B.first] at hxk
    exact (not_le_of_gt hx.1) hxk
  let n : Fin N := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hp := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    exact hp ⟨by omega, le_of_not_gt hn⟩
  · have heq : n.succ = (⟨Nat.find hex, by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by dsimp [n]; omega)
    rwa [heq]

/-- [internal]
At the final cutoff every cylinder has finished, even when the final
connector is partial. The literal clipped sum is its full variation sum.
This includes the empty finite history. Constants: none. -/
theorem clipped_variation_final {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (T : Fin N → ℝ) (hT : ∀ n, 0 ≤ T n)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n))
    (hends : ∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n)
    (hgraph : ∀ n, ∀ s ∈ Icc 0 (T n), vb ((γ n).U s) = (γ n).V s) :
    (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0
      (max 0 (min (T n) (cylinderClock S vb (B.cuts n.castSucc) b)))).toReal) =
      ∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal := by
  have hfirst (i : Fin (N + 1)) : a ≤ B.cuts i :=
    B.first.ge.trans (B.ordered (Fin.zero_le i))
  have hlast (i : Fin (N + 1)) : B.cuts i ≤ b :=
    (B.ordered (Fin.le_last i)).trans B.last.le
  have hab : a ≤ b := (hfirst _).trans B.last.le
  apply Finset.sum_congr rfl
  intro n _
  have hcool : B.cool n ∈ Icc a b :=
    ⟨(hfirst _).trans (B.split n).1, (B.split n).2.trans (hlast _)⟩
  have hseg : Icc ((γ n).U 0) ((γ n).U (T n)) ⊆ Icc a b := by
    rw [(hends n).1, (hends n).2]
    exact Icc_subset_Icc (hfirst _) hcool.2
  have hc := cylinder_clock_at_parameter h (hT n) (γ n) vb
    (B.cont.mono hseg) (fun u hu => B.mem u (hseg hu)) (hgraph n)
    (right_mem_Icc.mpr (hT n))
  rw [(hends n).1, (hends n).2] at hc
  have hle : T n ≤ cylinderClock S vb (B.cuts n.castSucc) b := by
    rw [← hc]
    exact monotoneOn_cylinderClock h B ⟨hfirst _, hlast _⟩ hcool ⟨hab, le_rfl⟩ hcool.2
  rw [min_eq_left hle, max_eq_right (hT n)]

end EmcsfAcExtension.Global.Closure
