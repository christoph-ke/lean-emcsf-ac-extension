module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Terminal.OpticalUpper

/-! # The proper limit of the shrinking boundary

Finite boundary records, the radius schedule and the radius stop are
explicit inputs until the shrinking construction is finished.
Source: charged_SF_new_version.tex:L4115–4120.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Restart

/-- [internal]
Conditional support for `sec:charged-closure#proper-axis-limit`.
The increasing shrinking boundary reaches an existing proper axis point.
The finite records and the two radius conclusions are supplied by closure;
`Rmin` is any fixed positive retained terminal radius. No constant is chosen.
Source: charged_SF_new_version.tex:L4115–4120. -/
theorem proper_axis_limit_of_closure (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {u₀ v₀ ρ b₀ Rmin : ℝ} (hu₀ : u₀ ∈ Ioo ui 0)
    (hρ : 0 ≤ ρ ∧ ρ < 1) (hRmin : 0 < Rmin)
    (U : ℕ → ℝ) (vb : ℝ → ℝ)
    (B : ∀ N, FiniteBoundary S ui u₀ (U N) v₀ ρ vb N)
    (hU : Monotone U)
    (hstart : u₀ ≤ U 0)
    (hR : ∀ n, Rmin ≤ S.r (U n) 0)
    (hrad : ∀ n, S.r (U n) (vb (U n)) = stageRadius ρ b₀ n) :
    ∃ us ∈ Ioo ui 0, Tendsto U atTop (𝓝 us) ∧
      Tendsto (fun n => vb (U n)) atTop (𝓝 us) := by
  let V := fun n => vb (U n)
  have hentry (n : ℕ) : u₀ ≤ U n := hstart.trans (hU (Nat.zero_le n))
  have hmem (n : ℕ) : (U n, V n) ∈ origDomain ui :=
    (B n).mem _ ⟨hentry n, le_rfl⟩
  have hV : Monotone V := by
    intro n m hnm
    exact (B m).mono ⟨hentry n, hU hnm⟩ ⟨hentry m, le_rfl⟩ (hU hnm)
  have hUb : BddAbove (range U) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.1.le⟩
  have hVb : BddAbove (range V) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hmem n).2.2.2⟩
  let us := ⨆ n, U n
  let vs := ⨆ n, V n
  have hTu : Tendsto U atTop (𝓝 us) := tendsto_atTop_ciSup hU hUb
  have hTv : Tendsto V atTop (𝓝 vs) := tendsto_atTop_ciSup hV hVb
  have hu0 : u₀ ≤ us := hstart.trans (le_ciSup hUb 0)
  have hu_le : us ≤ 0 := ciSup_le (fun n => (hmem n).2.1.le)
  have hv_le : vs ≤ 0 := ciSup_le (fun n => (hmem n).2.2.2)
  have huv : us ≤ vs := ciSup_le (fun n =>
    (hmem n).2.2.1.trans (le_ciSup hVb n))
  have hu_neg : us < 0 := by
    by_contra hn
    have he : us = 0 := le_antisymm hu_le (le_of_not_gt hn)
    have hT0 : Tendsto U atTop (𝓝[<] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨he ▸ hTu,
        Eventually.of_forall (fun n => (hmem n).2.1)⟩
    have hz := (Terminal.terminal_radius_collapse h.ui_neg h.solution h.mu).comp hT0
    have hh : Rmin ≤ 0 := ge_of_tendsto hz (Eventually.of_forall hR)
    exact (not_le_of_gt hRmin) hh
  have hp : (us, vs) ∈ origDomain ui :=
    ⟨hu₀.1.le.trans hu0, hu_neg, huv, hv_le⟩
  have hcont := (h.solution.cont_r (us, vs) hp).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr
      ⟨hTu.prodMk_nhds hTv, Eventually.of_forall hmem⟩)
  have hzero : Tendsto (fun n => S.r (U n) (V n)) atTop (𝓝 0) := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ.1 hρ.2).mul_const b₀
    simpa only [zero_mul, ← stageRadius_def, ← hrad] using ht
  have hr : S.r us vs = 0 := tendsto_nhds_unique hcont hzero
  have heq : us = vs := by
    apply le_antisymm huv
    by_contra hn
    exact (ne_of_gt (h.solution.r_pos (us, vs) hp (lt_of_not_ge hn))) hr
  exact ⟨us, ⟨hu₀.1.trans_le hu0, hu_neg⟩, hTu, heq.symm ▸ hTv⟩

end EmcsfAcExtension.Global.Restart
