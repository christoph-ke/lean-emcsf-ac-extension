module

public import EmcsfAcExtension.Global.Observation.WrappersExact
import Mathlib

/-! # Both characteristic integrations of the electric source

The inverse-cube second integral, logarithmic second integral and full
same-triangle integral have uniform numerical bounds. The optical Jacobians
are derived from the actual chart. Source: charged_SF_new_version.tex:L2463–2475.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal] The omitted inverse-cube second integral and its combination
with the retained logarithm. Both coefficients are universal. -/
theorem electric_second_integrals {r L eta : ℝ}
    (hr : 0 < r) (hrL : r ≤ L) (heta : 0 ≤ eta) :
    (∫ s in r..L, eta / s ^ 3) ≤ eta / (2 * r ^ 2) ∧
    (∫ s in r..L, eta / s ^ 3 + eta / L * Real.log (L / s)) ≤
      eta / (2 * r ^ 2) + eta := by
  have hL : 0 < L := hr.trans_le hrL
  have ci : ContinuousOn (fun s : ℝ => 1 / s ^ 3) (Icc r L) :=
    continuousOn_const.div (continuousOn_id.pow 3)
      (fun s hs => pow_ne_zero 3 (hr.trans_le hs.1).ne')
  have cl : ContinuousOn (fun s : ℝ => Real.log (L / s)) (Icc r L) :=
    (continuousOn_const.div continuousOn_id (fun s hs => (hr.trans_le hs.1).ne')).log
      (fun s hs => (div_pos hL (hr.trans_le hs.1)).ne')
  have hcube : (∫ s in r..L, eta / s ^ 3) ≤ eta / (2 * r ^ 2) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul]
    have heq := integral_inv_cube_outer hr hrL
    simp only [one_div] at heq
    rw [heq]
    have hh : 0 ≤ eta * (1 / (2 * L ^ 2)) := by positivity
    linear_combination hh
  refine ⟨hcube, ?_⟩
  rw [intervalIntegral.integral_add
    (by simpa only [div_eq_mul_inv, one_div, one_mul] using (ci.intervalIntegrable_of_Icc (μ :=
          volume) hrL).const_mul eta)
    ((cl.intervalIntegrable_of_Icc (μ := volume) hrL).const_mul (eta / L)),
    intervalIntegral.integral_const_mul]
  exact add_le_add hcube (electric_source_integrals hr hrL heta).2

private theorem ofReal_interval_integral {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hi : IntervalIntegrable f volume a b) (h0 : ∀ s ∈ Icc a b, 0 ≤ f s) :
    ENNReal.ofReal (∫ s in a..b, f s) = ∫⁻ s in Icc a b, ENNReal.ofReal (f s) := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs; exact h0 s hs)

/-- [internal] The full two-characteristic electric kernel on every actual
triangle is at most `96 eta`. The single incoming integral retains the log;
its outgoing inverse-cube and logarithmic pieces are both integrated.
The numerical constant is independent of all fields, scales and windows. -/
theorem electric_triangle_of_normalization
    {Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e : ℝ}
    {S : Fields} {D : Set (ℝ × ℝ)} {H P : ℂ}
    {phiStar yStar : ℝ → ℂ} {mStar : ℝ → ℝ}
    (hLzero : 1 ≤ Lzero)
    (h : OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e) :
    ∀ p ∈ sidewaysTruncation S D a b Lzero L,
      ((∫ u in p.2..p.1, eta / S.r u p.2 ^ 4 + eta / (L * S.r u p.2)) ≤
        8 * eta / S.r p.1 p.2 ^ 3 + 8 * eta / L * Real.log (L / S.r p.1 p.2)) ∧
      (∫⁻ v in Icc p.2 p.1, ∫⁻ u in Icc v p.1,
        ENNReal.ofReal (eta / S.r u v ^ 4 + eta / (L * S.r u v))) ≤ ENNReal.ofReal (96 * eta) := by
  let R := sidewaysTruncation S D a b Lzero L
  have hLp : 0 < L := (zero_lt_one.trans_le hLzero).trans_le h.ordered
  have heta := h.errors.2.1
  let f := fun r => eta / r ^ 4 + eta / (L * r)
  let g := fun r => 8 * eta / r ^ 3 + 8 * eta / L * Real.log (L / r)
  rcases h.fields with ⟨cr, cn, cl, _ca, _cp, _ct, _cm, _cq⟩
  have cf : ContinuousOn f (Icc Lzero L) :=
    (continuousOn_const.div (continuousOn_id.pow 4)
      (fun r hr => pow_ne_zero 4 (zero_lt_one.trans_le (hLzero.trans hr.1)).ne')).add
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun r hr => mul_ne_zero hLp.ne' (zero_lt_one.trans_le (hLzero.trans hr.1)).ne'))
  have cg : ContinuousOn g (Icc Lzero L) :=
    (continuousOn_const.div (continuousOn_id.pow 3)
      (fun r hr => pow_ne_zero 3 (zero_lt_one.trans_le (hLzero.trans hr.1)).ne')).add
      (((continuousOn_const.div continuousOn_id
        (fun r hr => (zero_lt_one.trans_le (hLzero.trans hr.1)).ne')).log
        (fun r hr => (div_pos hLp (zero_lt_one.trans_le (hLzero.trans hr.1))).ne')).const_mul _)
  have f0 (r) (hr : r ∈ Icc Lzero L) : 0 ≤ f r := by
    dsimp only [f]; have hp := zero_lt_one.trans_le (hLzero.trans hr.1); positivity
  have g0 (r) (hr : r ∈ Icc Lzero L) : 0 ≤ g r := by
    dsimp only [g]
    have hp := zero_lt_one.trans_le (hLzero.trans hr.1)
    have hh := Real.log_nonneg ((one_le_div hp).mpr hr.2)
    positivity
  have inc (p) (hp : p ∈ R) :
      (∫ u in p.2..p.1, f (S.r u p.2)) ≤ g (S.r p.1 p.2) := by
    have path := (sidewaysTruncation_paths (h.triangles p hp)).1
    have sec := cn.comp (continuous_id.prodMk continuous_const).continuousOn path
    have hh := radial_section_integral_le (σ := -1) hp.1.2.2.1
      (fun u hu => (h.equations (u,p.2) (path u hu)).1) sec
      (fun u hu => (path u hu).2) cf f0
      (fun u hu => by
        change 1 ≤ 8 * (-1) * S.nu u p.2
        linarith only [(h.box (u,p.2) (path u hu)).1.2])
    rw [(h.boundary p.2 (path p.2 ⟨le_rfl,hp.1.2.2.1⟩)).1,
      intervalIntegral.integral_symm (a := S.r p.1 p.2) (b := L)] at hh
    have hk := incoming_kernel_integral (A := 0) (E := eta)
      (zero_lt_one.trans_le (hLzero.trans hp.2.1)) hp.2.2 (by norm_num) heta
    simp only [zero_div, zero_add] at hk
    have hh' : (∫ u in p.2..p.1, f (S.r u p.2)) ≤ 8 * (∫ r in (S.r p.1 p.2)..L, f r) := by
      convert hh using 1; ring
    exact hh'.trans ((mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 8)).trans_eq
        (by dsimp [g]; ring))
  intro p hp
  refine ⟨inc p hp, ?_⟩
  have path := (sidewaysTruncation_paths (h.triangles p hp)).2
  have sec := cl.comp (continuous_const.prodMk continuous_id).continuousOn path
  have crs := cr.comp (continuous_const.prodMk continuous_id).continuousOn path
  have cgs := cg.comp crs (fun v hv => (path v hv).2)
  calc
    _ ≤ ∫⁻ v in Icc p.2 p.1, ENNReal.ofReal (g (S.r p.1 v)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      have hvp := path v hv
      have pathIn := (sidewaysTruncation_paths (h.triangles (p.1,v) hvp)).1
      have cfi := cf.comp (cr.comp (continuous_id.prodMk continuous_const).continuousOn pathIn)
        (fun u hu => (pathIn u hu).2)
      change (∫⁻ u in Icc v p.1, ENNReal.ofReal (f (S.r u v))) ≤ _
      rw [← ofReal_interval_integral (f := fun u => f (S.r u v)) hv.2
        (cfi.intervalIntegrable_of_Icc hv.2) (fun u hu => f0 _ (pathIn u hu).2)]
      exact ENNReal.ofReal_le_ofReal (inc (p.1,v) hvp)
    _ = ENNReal.ofReal (∫ v in p.2..p.1, g (S.r p.1 v)) :=
      (ofReal_interval_integral hp.1.2.2.1 (cgs.intervalIntegrable_of_Icc hp.1.2.2.1)
        (fun v hv => g0 _ (path v hv).2)).symm
    _ ≤ ENNReal.ofReal (96 * eta) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := radial_section_integral_le (σ := 1) hp.1.2.2.1
        (fun v hv => (h.equations (p.1,v) (path v hv)).2.1) sec
        (fun v hv => (path v hv).2) cg g0
        (fun v hv => by
          change 1 ≤ 8 * 1 * S.lam p.1 v
          linarith only [(h.box (p.1,v) (path v hv)).2.1.1])
      rw [(h.boundary p.1 (path p.1 ⟨hp.1.2.2.1,le_rfl⟩)).1] at hh
      have hk := outgoing_kernel_integral (A := 0) (E := eta) (epsilon := 0)
        (hLzero.trans hp.2.1) hp.2.2 (by norm_num) heta (by norm_num)
      simp only [zero_div, mul_zero, zero_add, add_zero] at hk
      calc
        _ ≤ 8 * (∫ r in (S.r p.1 p.2)..L, g r) := by simpa only [mul_one] using hh
        _ ≤ 8 * (12 * eta) := mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = _ := by ring

end EmcsfAcExtension.Global.Observation
