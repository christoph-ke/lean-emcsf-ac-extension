module

public import EmcsfAcExtension.Local.Broad.GeometryWeights
public import EmcsfAcExtension.Local.Broad.Charge
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Electric-square majorants for normalized scalar transport

The undifferenced majorants have two powers of the actual radius. The
second solution is compared with the first only after this cancellation.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- Undifferenced electric-square bounds in a common geometric box.
All coefficients are explicit functions of `c,C`, uniformly in the
triangle, coupling, scalar bound and both solutions. -/
theorem electric_square_pointwise_bounds {s t e M ε c C u v : ℝ} {S₁ S₂ : Fields}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbox : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε)
    (hσ : e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1)
    (hp : (u, v) ∈ triangle s t) :
    let B := e ^ 2 * M ^ 2 * ε ^ 2
    (0 ≤ S₁.Q u v ^ 2 / S₁.r u v ^ 2 ∧
      S₁.Q u v ^ 2 / S₁.r u v ^ 2 ≤ B * S₁.r u v ^ 2) ∧
    (0 ≤ S₂.Q u v ^ 2 / S₂.r u v ^ 2 ∧
      S₂.Q u v ^ 2 / S₂.r u v ^ 2 ≤ B * (C / c) ^ 2 * S₁.r u v ^ 2) ∧
    S₂.Q u v ^ 2 / S₂.r u v ^ 2 ≤ 4 * C ^ 2 := by
  intro B
  have hs : outSeg u u v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hself {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) :
      0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 ∧ S.Q u v ^ 2 / S.r u v ^ 2 ≤ B * S.r u v ^ 2 := by
    refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
    have hq := charge_bound hS hp.2.1 hs
      (fun x hx => (hbox S hm (u, x) (hs ⟨rfl, hx⟩)).2.2.1)
      (fun x hx => (hbox S hm (u, x) (hs ⟨rfl, hx⟩)).2.2.2)
    have hraw : |S.Q u v| ≤ (|e| * M * ε) * S.r u v ^ 2 := by
      apply hq.trans
      have hh : 0 ≤ |e| * M * ε * S.r u v ^ 2 := by positivity
      linarith
    have hh := electric_square_le_of_charge_bound (by positivity : 0 ≤ |e| * M * ε) hraw
    simpa only [mul_pow, sq_abs, B] using hh
  have h₁ := hself hS₁ (by simp)
  have h₂ := hself hS₂ (by simp)
  have hr0 {S : Fields} (hS : IsSolution e S (triangle s t)) : 0 ≤ S.r u v := by
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with h | h
    · subst v; exact (hS.axis u hp).1.symm.le
    · exact (hS.r_pos (u, v) hp h).le
  have hr₁ := hr0 hS₁
  have hr₂ := hr0 hS₂
  have hr := radius_comparison_of_solution_box hc hC hS₁ hS₂
    (fun S hm p hp => ⟨(hbox S hm p hp).1, (hbox S hm p hp).2.1⟩) hp
  have hR := outgoing_radius_upper hS₂ hp.2.1 hs
    (fun x hx => (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.1)
  have hR' : S₂.r u v ≤ C * (t - s) :=
    hR.trans (mul_le_mul_of_nonneg_left (by linarith [hp.1, hp.2.2] : v - u ≤ t - s) hC)
  have hst : 0 ≤ t - s := by linarith [hp.1, hp.2.1, hp.2.2]
  have hsquare : S₂.r u v ^ 2 ≤ (C * (t - s)) ^ 2 :=
    (sq_le_sq₀ hr₂ (mul_nonneg hC hst)).mpr hR'
  have hεsq : ε ^ 2 ≤ 1 := by simpa only [one_pow] using (sq_le_sq₀ hε zero_le_one).mpr hε1
  refine ⟨h₁, ⟨h₂.1, h₂.2.trans ?_⟩, h₂.2.trans ?_⟩
  · calc
      B * S₂.r u v ^ 2 ≤ B * ((C / c) * S₁.r u v) ^ 2 := by
        gcongr
        exact hr.2
      _ = _ := by ring
  · calc
      B * S₂.r u v ^ 2 ≤ B * (C * (t - s)) ^ 2 := by gcongr
      _ = 4 * C ^ 2 * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2 := by dsimp [B]; ring
      _ ≤ 4 * C ^ 2 * 1 * 1 := by gcongr
      _ = _ := by ring

end EmcsfAcExtension.Local.Broad
