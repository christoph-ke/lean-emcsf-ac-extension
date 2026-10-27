module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Electromagnetic curvature primitives

The outgoing bound is `charged_SF_new_version.tex:L4654–L4659`; the incoming orientation
is the approved repair in internal project record, equation (15).
The estimates use the primitive integrals themselves, so require no pending
field-level curvature identity.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem norm_em_integrand_le {c q r e M ε : ℝ} {p z : ℂ}
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (_hr : 0 ≤ r)
    (hq : |q| ≤ 2 * |e| * M * ε * r ^ 2)
    (hq2 : q ^ 2 / r ^ 2 ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 * r ^ 2)
    (hp : ‖p‖ ≤ M) (hz : ‖z‖ ≤ 4 * ε * |c|) (κ : ℂ) (hκ : ‖κ‖ = 1) :
    ‖((c * q ^ 2 / r ^ 2 : ℝ) : ℂ) + κ * e * q * z * starRingEnd ℂ p‖ ≤
      12 * e ^ 2 * M ^ 2 * ε ^ 2 * |c| * r ^ 2 := by
  have hscalar : ‖((c * q ^ 2 / r ^ 2 : ℝ) : ℂ)‖ ≤
      4 * e ^ 2 * M ^ 2 * ε ^ 2 * |c| * r ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, mul_div_assoc, abs_mul,
      abs_of_nonneg (div_nonneg (sq_nonneg q) (sq_nonneg r))]
    convert mul_le_mul_of_nonneg_left hq2 (abs_nonneg c) using 1
    ring
  have hcross : ‖κ * e * q * z * starRingEnd ℂ p‖ ≤
      8 * e ^ 2 * M ^ 2 * ε ^ 2 * |c| * r ^ 2 := by
    simp only [norm_mul, hκ, one_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    calc
      _ ≤ |e| * (2 * |e| * M * ε * r ^ 2) * (4 * ε * |c|) * M := by
        gcongr
      _ = _ := by rw [← sq_abs e]; ring
  exact (norm_add_le _ _).trans (by linarith only [hscalar, hcross])

private theorem integral_primitive_bound {a b A R : ℝ} {f : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (_hA : 0 ≤ A) (hR : 0 < R)
    (hf : AEStronglyMeasurable f (volume.restrict (Icc a b)))
    (hw : IntervalIntegrable w volume a b)
    (hb : ∀ x ∈ Icc a b, ‖f x‖ ≤ A * w x)
    (hm : (∫ x in a..b, w x) = R ^ 3 / 3) :
    ‖(R : ℂ)⁻¹ * ∫ x in a..b, f x‖ ≤ A / 3 * R ^ 2 := by
  have hAw := hw.const_mul A
  have hi : IntegrableOn f (Icc a b) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hAw).mono' hf (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hb x hx)
  have hin := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi
  have hle := (intervalIntegral.norm_integral_le_integral_norm hab).trans
    (intervalIntegral.integral_mono_on hab hin.norm hAw hb)
  rw [intervalIntegral.integral_const_mul, hm] at hle
  calc
    _ = R⁻¹ * ‖∫ x in a..b, f x‖ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ R⁻¹ * (A * (R ^ 3 / 3)) := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hR.le)
    _ = _ := by field_simp

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem out_em_bound (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvs : v ≤ s) :
    ‖curvEM e S u v‖ ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
  have hseg : outSeg u u v ⊆ triangle 0 s := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu, hx.1, hx.2.trans hvs⟩
  have hS := hset.c1.toIsSolution hset.pos
  have cr := continuousOn_out_section hS.cont_r hseg
  have cl := continuousOn_out_section hS.cont_lam hseg
  have cq := (continuousOn_out_section hS.cont_Q hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have cp := (continuousOn_out_section hS.cont_phi hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have ct := (continuousOn_out_section hS.cont_theta hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have ar := cr.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have al := cl.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hf : AEStronglyMeasurable (fun x =>
      (((S.lam u x * S.Q u x ^ 2 / S.r u x ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u x * S.theta u x * starRingEnd ℂ (S.phi u x)))
      (volume.restrict (Icc u v)) := by
    have ax := (al.mul (cq.pow 2)).div₀ (ar.pow 2)
    have ac := Complex.continuous_ofReal.comp_aestronglyMeasurable ax
    have aq := Complex.continuous_ofReal.comp_aestronglyMeasurable cq
    exact ac.sub (((aq.const_mul (I * (e : ℂ))).mul ct).mul cp.star)
  have hb (x : ℝ) (hx : x ∈ Icc u v) :
      ‖(((S.lam u x * S.Q u x ^ 2 / S.r u x ^ 2 : ℝ) : ℂ) -
        I * e * S.Q u x * S.theta u x * starRingEnd ℂ (S.phi u x))‖ ≤
      (12 * e ^ 2 * M ^ 2 * ε ^ 2) * (S.lam u x * S.r u x ^ 2) := by
    have hp : (u, x) ∈ triangle 0 s := ⟨hu, hx.1, hx.2.trans hvs⟩
    have hl := hset.c1.lam_pos (u, x) hp
    have he := norm_em_integrand_le (c := S.lam u x)
      (le_trans (by norm_num) hset.one_le_M) hset.eps_nonneg
      (hset.radius_nonneg hp) (hset.charge_le hp) (hset.charge_sq_div_le hp)
      (hset.box (u, x) hp).2.2.2.2.2.1
      (by simpa only [abs_of_pos hl] using hset.theta_norm_le hp) (-I) (by simp)
    simpa only [neg_mul, add_neg_cancel_right, sub_eq_add_neg, abs_of_pos hl, mul_assoc] using he
  have hm := outgoing_radius_moment hS huv.le hseg 2
  change ‖(S.r u v : ℂ)⁻¹ * _‖ ≤ _
  convert integral_primitive_bound huv.le (by positivity)
    (hset.c1.r_pos (u, v) ⟨hu, huv.le, hvs⟩ huv) hf
    (ContinuousOn.intervalIntegrable_of_Icc huv.le (cl.mul (cr.pow 2))) hb
    (by
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hm
      simpa only [Pi.mul_apply, Pi.pow_apply] using hm) using 1
  ring

/-- [node restart-bv-C-charge]
Outgoing electromagnetic curvature primitive (`charged_SF_new_version.tex:L4654–L4659`).
`C` is universal, independent of `e`, `s`, `M`, and all higher data norms;
no smallness is needed. -/
theorem bv_c_charge : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ∀ u v, 0 ≤ u → u < v → v ≤ s →
      ‖curvEM e S u v‖ ≤ C * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 :=
  ⟨4, by norm_num, fun _ _ _ _ _ _ hset _ _ hu huv hvs => out_em_bound hset hu huv hvs⟩

/-- Exact incoming radial power moment on a shortened axis-to-point section.
There is no estimate constant and no smallness hypothesis. -/
theorem incoming_radius_moment (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) (n : ℕ) :
    (∫ x in u..v, -S.nu x v * S.r x v ^ n) = S.r u v ^ (n + 1) / (n + 1) := by
  have hm : MapsTo (fun x => (x, v)) (Icc u v) (triangle 0 s) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvs⟩
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hm
  have cn := hset.c1.c1_nu.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hm
  have hd (x : ℝ) (hx : x ∈ Ioo u v) : HasDerivAt
      (fun x => -(S.r x v ^ (n + 1) / (n + 1))) (-S.nu x v * S.r x v ^ n) x := by
    have dr := (hasDerivWithinAt_pdU hset.c1.c1_r (hm ⟨hx.1.le, hx.2.le⟩) hm).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
    rw [(hset.c1.eq_u (x, v) (hm ⟨hx.1.le, hx.2.le⟩) hx.2).1] at dr
    convert ((dr.pow (n + 1)).div_const (n + 1 : ℝ)).neg using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv
    (cn.neg.mul (cr.pow n))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    (((cr.pow (n + 1)).div_const _).neg) hd hi
  simpa [(hset.c1.axis v ⟨hu.trans huv, le_rfl, hvs⟩).1] using hftc

private theorem in_em_bound (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvs : v ≤ s) :
    ‖(S.r u v : ℂ)⁻¹ * ∫ x in u..v,
      (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
        I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))‖ ≤
      4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
  have hseg : inSeg u v v ⊆ triangle 0 s := by
    rintro ⟨x, y⟩ ⟨hux, hxv, rfl⟩
    exact ⟨hu.trans hux, hxv, hvs⟩
  have hS := hset.c1.toIsSolution hset.pos
  have cr := continuousOn_in_section hS.cont_r hseg
  have cn := continuousOn_in_section hS.cont_nu hseg
  have cq := (continuousOn_in_section hS.cont_Q hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have cp := (continuousOn_in_section hS.cont_phi hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have ct := (continuousOn_in_section hS.cont_xi hseg).aestronglyMeasurable
    (μ := volume) measurableSet_Icc
  have ar := cr.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have an := cn.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hf : AEStronglyMeasurable (fun x =>
      (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
        I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v)))
      (volume.restrict (Icc u v)) := by
    have ax := (an.mul (cq.pow 2)).div₀ (ar.pow 2)
    have ac := Complex.continuous_ofReal.comp_aestronglyMeasurable ax
    have aq := Complex.continuous_ofReal.comp_aestronglyMeasurable cq
    exact ac.add (((aq.const_mul (I * (e : ℂ))).mul ct).mul cp.star)
  have hb (x : ℝ) (hx : x ∈ Icc u v) :
      ‖(((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
        I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))‖ ≤
      (12 * e ^ 2 * M ^ 2 * ε ^ 2) * (-S.nu x v * S.r x v ^ 2) := by
    have hp : (x, v) ∈ triangle 0 s := ⟨hu.trans hx.1, hx.2, hvs⟩
    have hn := hset.c1.nu_neg (x, v) hp
    have he := norm_em_integrand_le (c := S.nu x v)
      (le_trans (by norm_num) hset.one_le_M) hset.eps_nonneg
      (hset.radius_nonneg hp) (hset.charge_le hp) (hset.charge_sq_div_le hp)
      (hset.box (x, v) hp).2.2.2.2.2.1
      (by simpa only [abs_of_neg hn] using hset.xi_norm_le hp) I (by simp)
    simpa only [abs_of_neg hn, mul_assoc] using he
  convert integral_primitive_bound huv.le (by positivity)
    (hset.c1.r_pos (u, v) ⟨hu, huv.le, hvs⟩ huv) hf
    (ContinuousOn.intervalIntegrable_of_Icc huv.le (cn.neg.mul (cr.pow 2))) hb
    (by
      have hm := incoming_radius_moment hset hu huv.le hvs 2
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at hm
      simpa only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply] using hm)
    using 1
  ring

/-- [node restart-sec-independent-area#incoming-curvature-charge]
Incoming electromagnetic curvature primitive, with its axis orientation made
explicit (approved internal project record equation (15); `charged_SF_new_version.tex:L4660`). `C`
is
universal, independent of `e`, `s`, `M`, and all higher data norms. The overall
minus sign in the incoming curvature representation has the same norm. -/
theorem Area.incoming_curvature_charge :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ∀ u v, 0 ≤ u → u < v → v ≤ s →
      ‖(S.r u v : ℂ)⁻¹ * ∫ x in u..v,
        (((S.nu x v * S.Q x v ^ 2 / S.r x v ^ 2 : ℝ) : ℂ) +
          I * e * S.Q x v * S.xi x v * starRingEnd ℂ (S.phi x v))‖ ≤
        C * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 :=
  ⟨4, by norm_num, fun _ _ _ _ _ _ hset _ _ hu huv hvs => in_em_bound hset hu huv hvs⟩

end EmcsfAcExtension.Local
