module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Observation.ChartDomains
public import EmcsfAcExtension.Global.Observation.ChartEquations
public import EmcsfAcExtension.Global.Observation.BoundaryCharts

/-! # Proper comparison windows and stopped characteristic travel

The inward region is the literal `comparisonDomain`, as ratified in internal project record.
The positive-radius truncations remain inside the original proper label
rectangle. Travel estimates use normalized expansion bounds only while the
target radius has not been reached. Source: `charged_SF_new_version.tex:L2741–L2755` and
internal project record, comparison-window (D1)–(D4).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
The literal inward comparison region lies in the source characteristic
triangle. This is a set identity consequence, with no optical assumption. -/
theorem comparisonDomain_subset_triangle (S : Fields) (ui : ℝ) (U V : ℝ → ℝ)
    (s t b : ℝ) :
    comparisonDomain S (origDomain ui) U V s t b ⊆ triangle (U s) (V t) := by
  intro p hp
  exact ⟨hp.1.2.1.1, hp.1.1.2.2.1, hp.1.2.2.2⟩

private theorem stopped_radius_decrease
    {r w : ℝ → ℝ} {a b c ρ : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn r (Icc a b))
    (hρ : ∀ x ∈ Icc a b, ρ ≤ r x)
    (hd : ∀ x ∈ Ioo a b, ρ ≤ r x → HasDerivAt r (w x) x ∧ w x ≤ -c) :
    r b - r a ≤ -c * (b - a) := by
  apply (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc
    (fun x hx => by
      rw [interior_Icc] at hx
      exact (hd x hx (hρ x (Ioo_subset_Icc_self hx))).1.differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      obtain ⟨hderiv, hbound⟩ := hd x hx (hρ x (Ioo_subset_Icc_self hx))
      simpa only [hderiv.deriv] using hbound)
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab

/-- [internal]
A complete incoming ray reaches a positive target before either its existing
axis endpoint or a label budget `L/c`. The speed bound is needed only above
the target. The unique hit has travel at most `(L-ρ)/c`. The disjunction
expresses the two endpoints allowed by internal project record, and rules out an unrelated
interior endpoint. All constants are fixed before this ray. -/
theorem radius_hit_of_stopped_travel
    {r w : ℝ → ℝ} {a b c L ρ : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hρ : 0 < ρ) (hρL : ρ ≤ L)
    (hcont : ContinuousOn r (Icc a b)) (hanti : StrictAntiOn r (Icc a b))
    (hstart : r a = L)
    (hend : r b ≤ ρ ∨ L / c ≤ b - a)
    (hd : ∀ x ∈ Ioo a b, ρ ≤ r x → HasDerivAt r (w x) x ∧ w x ≤ -c) :
    ∃ u ∈ Icc a b, r u = ρ ∧ u - a ≤ (L - ρ) / c ∧
      ∀ z ∈ Icc a b, r z = ρ → z = u := by
  have hbracket : r b ≤ ρ := by
    rcases hend with h | hbudget
    · exact h
    · by_contra h
      have hb : ρ < r b := lt_of_not_ge h
      have hcut (x : ℝ) (hx : x ∈ Icc a b) : ρ ≤ r x :=
        hb.le.trans (hanti.antitoneOn hx (right_mem_Icc.mpr hab) hx.2)
      have hdrop := stopped_radius_decrease hab hcont hcut hd
      have hlength : L ≤ c * (b - a) := by
        simpa only [mul_comm] using (div_le_iff₀ hc).mp hbudget
      rw [hstart] at hdrop
      nlinarith only [hdrop, hlength, hb, hρ]
  obtain ⟨u, hu, hru⟩ := intermediate_value_Icc' hab hcont
    ⟨hbracket, by simpa only [hstart] using hρL⟩
  have hsub : Icc a u ⊆ Icc a b := Icc_subset_Icc le_rfl hu.2
  have hdrop := stopped_radius_decrease hu.1 (hcont.mono hsub)
    (fun x hx => by
      rw [← hru]
      exact hanti.antitoneOn (hsub hx) hu hx.2)
    (fun x hx => hd x ⟨hx.1, hx.2.trans_le hu.2⟩)
  refine ⟨u, hu, hru, ?_, fun z hz heq => hanti.injOn hz hu (heq.trans hru.symm)⟩
  apply (le_div_iff₀ hc).mpr
  rw [hstart, hru] at hdrop
  nlinarith only [hdrop]

/-- [internal]
Reserve two characteristic travel margins uniformly in the outer radius.
`B,T` depend only on the fixed expansion lower bound, inner radius and
requested inner clock length. They precede every outer radius and label.
This is the arithmetic choice (D4); the level-curve construction still has
to supply its clock and the stopped rays. -/
theorem comparison_window_margins {c L₀ K : ℝ}
    (hc : 0 < c) (hL₀ : 0 < L₀) (hK : 0 < K) :
    ∃ B > 0, ∃ T > 0, K ≤ 2 * c * B ∧
      ∀ L ≥ L₀, ∀ v ∈ Icc (-B) B,
        -T * L < v - L / c ∧ v + L / c < T * L := by
  let B := K / (2 * c)
  let T := 1 / c + B / L₀ + 3
  have hB : 0 < B := div_pos hK (by positivity)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨B, hB, T, hT, ?_, ?_⟩
  · dsimp only [B]
    rw [mul_div_cancel₀ _ (by positivity : 2 * c ≠ 0)]
  · intro L hL v hv
    have hLp : 0 < L := hL₀.trans_le hL
    have hBL : B ≤ B / L₀ * L := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hL₀).mpr (mul_le_mul_of_nonneg_left hL hB.le)
    have hid : T * L = L / c + B / L₀ * L + 3 * L := by dsimp only [T]; ring
    constructor <;> nlinarith only [hv.1, hv.2, hBL, hLp, hid]

/-- [internal]
The inner clock contains the requested full interval when its derivative
density is at least `2c` on the reserved outer-label segment. All-subsegment
clock equations supply the two displayed anchored integral forms. No inverse
clock or extension past either endpoint is presumed. There are no chosen
constants: `B` is the margin selected before the physical solution. -/
theorem inner_clock_window_of_speed {clock w : ℝ → ℝ} {B c K : ℝ}
    (hB : 0 ≤ B) (hK : K ≤ 2 * c * B)
    (hcont : ContinuousOn clock (Icc (-B) B)) (hzero : clock 0 = 0)
    (hleft : IntegralForm clock w (-B) 0) (hright : IntegralForm clock w 0 B)
    (hspeed : ∀ x ∈ Icc (-B) B, 2 * c ≤ w x) :
    Icc (-K) K ⊆ clock '' Icc (-B) B := by
  have hleftbound := intervalIntegral.integral_mono_on (by linarith only [hB] : -B ≤ 0)
    intervalIntegrable_const hleft.1
    (fun x hx => hspeed x ⟨hx.1, hx.2.trans hB⟩)
  have hrightbound := intervalIntegral.integral_mono_on hB
    intervalIntegrable_const hright.1
    (fun x hx => hspeed x ⟨(show -B ≤ 0 by linarith only [hB]).trans hx.1, hx.2⟩)
  rw [intervalIntegral.integral_const, ← hleft.2, hzero] at hleftbound
  rw [intervalIntegral.integral_const, ← hright.2, hzero] at hrightbound
  simp only [smul_eq_mul] at hleftbound hrightbound
  apply Subset.trans ?_ (intermediate_value_Icc (by linarith only [hB]) hcont)
  exact Icc_subset_Icc (by linarith only [hleftbound, hK])
    (by linarith only [hrightbound, hK])

end EmcsfAcExtension.Global.Observation
