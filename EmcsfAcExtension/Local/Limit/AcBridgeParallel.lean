module

public import EmcsfAcExtension.Local.Limit.AcBridgePhase
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Stability.PotentialDifferencePhase
import EmcsfAcExtension.Local.Limit.AcBridgeUniform
import EmcsfAcExtension.Infra.Mixed.SectionIntegral

/-! # Uniform convergence of the actual incoming parallel factors

internal project record item 7.5. The fixed coupling and section-length factors are retained
explicitly in the phase estimate. No derivative of the potential is used.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Uniform potential convergence gives uniform convergence of the unitary
incoming parallel factors. The explicit phase error is bounded by `|e|*T`
times the potential error, uniformly over the closed triangle. -/
theorem incoming_parallel_uniform_of_potential_uniform {e T : ℝ}
    {An : ℕ → ℝ → ℝ → ℝ} {A : ℝ → ℝ → ℝ} (hT : 0 < T)
    (hAn : ∀ n, ContinuousOn (Function.uncurry (An n)) (triangle 0 T))
    (hA : ContinuousOn (Function.uncurry A) (triangle 0 T))
    (hl : TendstoUniformlyOn (fun n => Function.uncurry (An n)) (Function.uncurry A) atTop (triangle
        0 T)) :
    TendstoUniformlyOn (fun n => Function.uncurry (incomingParallel e (An n)))
      (Function.uncurry (incomingParallel e A)) atTop (triangle 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ρ hρ
  let δ := ρ / (2 * (|e| * T + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hl) δ hδ] with n hn p hp
  have hm : MapsTo (fun s => (s,p.2)) (Icc 0 p.1) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2.trans hp.2.1, hp.2.2⟩
  have hi₁ : IntervalIntegrable (fun s => An n s p.2) volume 0 p.1 :=
    ((hAn n).comp (continuous_id.prodMk continuous_const).continuousOn hm).intervalIntegrable_of_Icc
        hp.1
  have hi₂ : IntervalIntegrable (fun s => A s p.2) volume 0 p.1 :=
    (hA.comp (continuous_id.prodMk continuous_const).continuousOn hm).intervalIntegrable_of_Icc hp.1
  have hbound : (∫ s in (0 : ℝ)..p.1, |An n s p.2 - A s p.2|) ≤ T * δ := by
    simpa only [Real.norm_eq_abs] using Mixed.integral_norm_section_le le_rfl hp.1
      (hp.2.1.trans hp.2.2) hδ.le (hi₁.sub hi₂) (fun s hs => by
        have hh := hn (s,p.2) (hm hs)
        simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using hh.le)
  have hh : ‖incomingParallel e (An n) p.1 p.2 - incomingParallel e A p.1 p.2‖ ≤ |e| * T * δ :=
    (stab_parallel_factor_sub_le hp.1 hi₁ hi₂ e).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (abs_nonneg e))
  have hlt : |e| * T * δ < ρ := by
    have hd : 0 < 2 * (|e| * T + 1) := by positivity
    dsimp only [δ]
    rw [← mul_div_assoc, div_lt_iff₀ hd]
    nlinarith only [hρ, mul_nonneg (abs_nonneg e) hT.le]
  change dist (incomingParallel e A p.1 p.2) (incomingParallel e (An n) p.1 p.2) < ρ
  rw [dist_comm, dist_eq_norm]
  exact hh.trans_lt hlt

/-- Uniform convergence of unit left factors and bounded right factors
passes to their products. The sole bound is on the limiting right factor;
its value is explicit and is used only for this qualitative analytic helper. -/
theorem unitary_product_uniform_of_uniform {T B : ℝ}
    {Pn bn : ℕ → ℝ → ℝ → ℂ} {P b : ℝ → ℝ → ℂ} (hB : 0 ≤ B)
    (hP : TendstoUniformlyOn (fun n => Function.uncurry (Pn n)) (Function.uncurry P) atTop (triangle
        0 T))
    (hb : TendstoUniformlyOn (fun n => Function.uncurry (bn n)) (Function.uncurry b) atTop (triangle
        0 T))
    (hunit : ∀ n p, p ∈ triangle 0 T → ‖Pn n p.1 p.2‖ = 1)
    (hbound : ∀ p ∈ triangle 0 T, ‖b p.1 p.2‖ ≤ B) :
    TendstoUniformlyOn (fun n p => Pn n p.1 p.2 * bn n p.1 p.2)
      (fun p => P p.1 p.2 * b p.1 p.2) atTop (triangle 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ρ hρ
  have hδ : 0 < ρ / (2 * (B+1)) := by positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hP) (ρ / (2*(B+1))) hδ,
    (Metric.tendstoUniformlyOn_iff.1 hb) (ρ/2) (by positivity)] with n hnP hnb p hp
  have heq : Pn n p.1 p.2 * bn n p.1 p.2 - P p.1 p.2 * b p.1 p.2 =
      Pn n p.1 p.2 * (bn n p.1 p.2 - b p.1 p.2) +
        (Pn n p.1 p.2 - P p.1 p.2) * b p.1 p.2 := by ring
  have hpa : ‖Pn n p.1 p.2 - P p.1 p.2‖ < ρ / (2*(B+1)) := by
    simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using hnP p hp
  have hba : ‖bn n p.1 p.2 - b p.1 p.2‖ < ρ / 2 := by
    simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using hnb p hp
  have hbound' : ρ / (2*(B+1)) * B ≤ ρ/2 := by
    have hh : B / (B+1) ≤ 1 := (div_le_one (by positivity : 0 < B+1)).2 (by linarith)
    calc
      _ = (ρ/2) * (B/(B+1)) := by field_simp
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ρ/2)
  rw [dist_comm, dist_eq_norm, heq]
  apply (norm_add_le _ _).trans_lt
  rw [norm_mul, norm_mul, hunit n p hp, one_mul]
  have hh := mul_le_mul hpa.le (hbound p hp) (norm_nonneg _) (by positivity : 0 ≤ ρ / (2*(B+1)))
  exact (add_le_add le_rfl hh).trans_lt (by linarith only [hba, hbound'])

end EmcsfAcExtension.Local
