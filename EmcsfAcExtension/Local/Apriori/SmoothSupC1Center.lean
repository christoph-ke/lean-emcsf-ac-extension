module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Apriori.SmoothSupCenter
import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Center orders with an explicit outgoing derivative budget

The scalar Hardy estimate is composed with the charge and mass constraints.
The quadratic dependence on the outgoing derivative bound is retained.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- An outgoing derivative budget `A` gives linear scalar decay, cubic charge
and mass, and quadratic mass ratio. Every coefficient is explicit and depends
only on `e,M,T`; the estimates are uniform in `ε,h,S,A` and include the axis.
In particular the mass ratio is `O(r² A²)`, with no incoming derivative budget. -/
theorem smooth_center_orders_of_outgoing_bound {e T ε M A : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h) (hA : 0 ≤ A)
    (hb : ∀ p ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a p.1 p.2‖ ≤ A) :
    ∀ p ∈ triangle 0 T,
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ 4 * A * S.r p.1 p.2 ∧
      |S.Q p.1 p.2| ≤ 8 * |e| * M * A * S.r p.1 p.2 ^ 3 ∧
      S.m p.1 p.2 ≤ 16 * (1 + 4 * e ^ 2 * M ^ 2 * T ^ 2) * A ^ 2 *
        S.r p.1 p.2 ^ 3 ∧
      S.mu p.1 p.2 ≤ 32 * (1 + 4 * e ^ 2 * M ^ 2 * T ^ 2) * A ^ 2 *
        S.r p.1 p.2 ^ 2 := by
  have hd (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ (4 * A) * S.r p.1 p.2 := by
    convert smooth_outgoing_decay_of_bound hset hA hb hp using 1
    ring
  intro p hp
  have hm := smooth_mass_center_of_bound hset (by positivity : 0 ≤ 4 * A) hd hp
  refine ⟨hd p hp, ?_, ?_, ?_⟩
  · convert smooth_charge_cubic_of_bound hset (by positivity : 0 ≤ 4 * A) hd hp using 1
    ring
  · convert hm.1 using 1
    ring
  · convert hm.2 using 1
    ring

/-- Center orders with a length cap fixed before the constructed apex.
The positive coefficient depends only on `e,R,M`, uniformly in the scalar
derivative budget `A`, local length, variation, datum and field. -/
theorem smooth_center_orders_uniform_of_outgoing_bound (e R M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T ε : ℝ) (S : Fields) (h : ℝ → ℂ), T ≤ R →
      AprioriSetting e T ε M S h → ∀ A : ℝ, 0 ≤ A →
      (∀ p ∈ triangle 0 T, ‖pdV (triangle 0 T) S.a p.1 p.2‖ ≤ A) →
      ∀ p ∈ triangle 0 T,
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ 4 * A * S.r p.1 p.2 ∧
        |S.Q p.1 p.2| ≤ C * A * S.r p.1 p.2 ^ 3 ∧
        S.m p.1 p.2 ≤ C * A ^ 2 * S.r p.1 p.2 ^ 3 ∧
        S.mu p.1 p.2 ≤ C * A ^ 2 * S.r p.1 p.2 ^ 2 := by
  let U := 1 + 4 * e ^ 2 * M ^ 2 * R ^ 2
  let C := 1 + 8 * |e| * M + 32 * U
  have hU : 0 < U := by dsimp only [U]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T ε S h hTR hset A hA hb p hp
  obtain ⟨hd, hq, hm, hμ⟩ := smooth_center_orders_of_outgoing_bound hset hA hb p hp
  have hr := hset.radius_nonneg hp
  have ht : T ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hset.pos.le hTR 2
  have hu : 1 + 4 * e ^ 2 * M ^ 2 * T ^ 2 ≤ U := by
    dsimp only [U]
    gcongr
  have hcq : 8 * |e| * M ≤ C := by dsimp only [C]; linarith only [hU.le]
  have hcm : 16 * (1 + 4 * e ^ 2 * M ^ 2 * T ^ 2) ≤ C := by
    have hh := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 16)
    dsimp only [C]
    nlinarith only [hh, hU.le, mul_nonneg (abs_nonneg e) hM]
  have hcμ : 32 * (1 + 4 * e ^ 2 * M ^ 2 * T ^ 2) ≤ C := by
    have hh := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 32)
    dsimp only [C]
    nlinarith only [hh, mul_nonneg (abs_nonneg e) hM]
  refine ⟨hd, hq.trans ?_, hm.trans ?_, hμ.trans ?_⟩
  · gcongr
  · gcongr
  · gcongr

end EmcsfAcExtension.Local
