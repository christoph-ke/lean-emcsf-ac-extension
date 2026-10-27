module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform products on compact domains and section L¹ bounds

Auxiliary analysis A6 of internal project record. Compactness and
continuity provide the boundedness needed for products of uniform limits.
A common section-mass bound turns uniform errors into uniform L¹ errors,
with the exact factor given by that bound (at most `T` on the fixed triangle).
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

/-- A6: products of uniformly convergent continuous functions on a compact set
converge uniformly. Compactness supplies all required bounds; there is no
independent multiplier-bound hypothesis. -/
theorem tendstoUniformlyOn_mul_of_isCompact {α : Type*} [TopologicalSpace α]
    {S : Set α} {F G : ℕ → α → ℂ} {f g : α → ℂ}
    (hS : IsCompact S) (hF : ∀ n, ContinuousOn (F n) S)
    (hG : ∀ n, ContinuousOn (G n) S)
    (hFlim : TendstoUniformlyOn F f atTop S) (hGlim : TendstoUniformlyOn G g atTop S) :
    TendstoUniformlyOn (fun n x => F n x * G n x) (fun x => f x * g x) atTop S := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hf := hFlim.continuousOn (Eventually.of_forall hF).frequently
  have hg := hGlim.continuousOn (Eventually.of_forall hG).frequently
  apply ((hf.mul hg).tendsto_domRestrict_iff_tendstoUniformlyOn
    (fun n => (hF n).mul (hG n))).1
  exact ((hf.tendsto_domRestrict_iff_tendstoUniformlyOn hF).2 hFlim).mul
    ((hg.tendsto_domRestrict_iff_tendstoUniformlyOn hG).2 hGlim)

/-- The explicit triangle-section length factor: for `0 ≤ a ≤ b ≤ T`, a norm
bound `A` gives an integral bound `T*A`. The same statement covers both incoming
and outgoing sections, with coefficient one independent of all data. -/
theorem integral_norm_section_le {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b T A : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hA : 0 ≤ A) (hf : IntervalIntegrable f volume a b)
    (hbound : ∀ x ∈ Icc a b, ‖f x‖ ≤ A) :
    (∫ x in a..b, ‖f x‖) ≤ T * A := by
  calc
    _ ≤ ∫ x in a..b, A := intervalIntegral.integral_mono_on hab hf.norm
      (intervalIntegrable_const) hbound
    _ = (b - a) * A := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hA

end EmcsfAcExtension.Mixed
