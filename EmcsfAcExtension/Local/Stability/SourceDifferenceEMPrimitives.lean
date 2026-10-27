module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitiveAlgebra
import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Mixed.SectionIntegral

/-! # Literal charged curvature primitive integrands

The named functions are precisely the integrands of the frozen internal
curvature split. Their normalized forms are used only off the axis.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The literal integrand of the outgoing charged curvature primitive. -/
@[expose] noncomputable def emPrimitiveOut (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  ((S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) -
    I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)

/-- The literal integrand of the incoming charged curvature primitive,
before its exterior negative inverse radius. -/
@[expose] noncomputable def emPrimitiveIn (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  ((S.nu u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) : ℂ) +
    I * e * S.Q u v * S.xi u v * starRingEnd ℂ (S.phi u v)

/-- Off-axis normalized outgoing charged integrand. No division by the
coupling or the small variation parameter is used in this identity. -/
theorem emPrimitiveOut_eq_normalized (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) :
    emPrimitiveOut e S u v = ((S.lam u v * S.r u v ^ 2 : ℝ) : ℂ) *
      (((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) ^ 2 +
        (-I * e) * ((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) *
          (S.theta u v / S.lam u v) * starRingEnd ℂ (S.phi u v)) := by
  have hrc := ofReal_ne_zero.mpr hr
  have hlc := ofReal_ne_zero.mpr hl
  dsimp [emPrimitiveOut]
  push_cast
  field_simp
  ; ring

/-- Off-axis normalized incoming charged integrand. Its current term has
the opposite sign to the outgoing primitive current term. -/
theorem emPrimitiveIn_eq_normalized (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0) :
    emPrimitiveIn e S u v = ((S.nu u v * S.r u v ^ 2 : ℝ) : ℂ) *
      (((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) ^ 2 +
        (I * e) * ((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) *
          (S.xi u v / S.nu u v) * starRingEnd ℂ (S.phi u v)) := by
  have hrc := ofReal_ne_zero.mpr hr
  have hnc := ofReal_ne_zero.mpr hn
  dsimp [emPrimitiveIn]
  push_cast
  field_simp

/-- Both individual charged primitive integrands have the universal bound
`2 e² M² ε² r²`, including the regular axis. This constant is independent
of all physical parameters, data, lengths and derivative suprema. -/
theorem emPrimitive_norm_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) (hε₁ : ε ≤ 1)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    ‖emPrimitiveOut e S u v‖ ≤ 2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 ∧
    ‖emPrimitiveIn e S u v‖ ≤ 2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
  rcases hp.2.1.eq_or_lt with huv | huv
  · change u = v at huv
    subst v
    have ha := hs.c1.axis u hp
    simp [emPrimitiveOut, emPrimitiveIn, ha.1, ha.2.2.1]
  have hr := hs.c1.r_pos (u, v) hp huv
  have hl := hs.c1.lam_pos (u, v) hp
  have hn := hs.c1.nu_neg (u, v) hp
  have hb := hs.box.2 (u, v) hp
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hb.2.2.2.2.2.1
  have hM : 0 ≤ M := zero_le_one.trans hs.box.1
  have hq : |S.Q u v / S.r u v ^ 2| ≤ |e| * M * ε := by
    have h := em_charge_bound_from_setting hs hp
    rw [abs_div, abs_of_pos (pow_pos hr 2)]
    apply (div_le_iff₀ (pow_pos hr 2)).2
    have hE : 0 ≤ |e| * M * ε * S.r u v ^ 2 := by positivity
    linarith only [h, hE]
  obtain ⟨_, _, hbracket⟩ := em_primitive_bracket_difference_le 1 1 (by norm_num) (by norm_num)
  have hbound (z c : ℂ) (hz : ‖z‖ ≤ ε) (hc : ‖c‖ ≤ |e|) :
      ‖((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) ^ 2 +
        c * ((S.Q u v / S.r u v ^ 2 : ℝ) : ℂ) * z * starRingEnd ℂ (S.phi u v)‖ ≤
          2 * e ^ 2 * M ^ 2 * ε ^ 2 := by
    have h := (hbracket |e| M ε 0 0 0 (S.Q u v / S.r u v ^ 2) (S.Q u v / S.r u v ^ 2)
      (S.phi u v) (S.phi u v) z z c (abs_nonneg _) hs.box.1 hε hε₁
      le_rfl le_rfl le_rfl hq hq (by simp) hb.2.2.2.2.2.2 hb.2.2.2.2.2.2
      (by simp) hz hz (by simp) hc).1
    simpa only [sq_abs] using h
  have hc : ‖I * (e : ℂ)‖ ≤ |e| := by simp only [norm_mul, norm_I, one_mul,
    norm_real, Real.norm_eq_abs, le_refl]
  have hcn : ‖-I * (e : ℂ)‖ ≤ |e| := by simpa only [neg_mul, norm_neg] using hc
  have hx := hbound (S.theta u v / S.lam u v) (-I * e)
    ((le_add_of_nonneg_right (norm_nonneg _)).trans hb.2.2.2.2.2.1) hcn
  have hy := hbound (S.xi u v / S.nu u v) (I * e)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans hb.2.2.2.2.2.1) hc
  rw [emPrimitiveOut_eq_normalized e S u v hr.ne' hl.ne',
    emPrimitiveIn_eq_normalized e S u v hr.ne' hn.ne]
  have hfactor (l : ℝ) (z : ℂ) (hl : |l| ≤ 1)
      (hz : ‖z‖ ≤ 2 * e ^ 2 * M ^ 2 * ε ^ 2) :
      ‖((l * S.r u v ^ 2 : ℝ) : ℂ) * z‖ ≤
        2 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (sq_nonneg (S.r u v))]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right hl (sq_nonneg _)) hz
      (norm_nonneg _) (by positivity)
    nlinarith only [h]
  exact ⟨hfactor _ _ (by simpa only [abs_of_pos hl] using hb.2.1) hx,
    hfactor _ _ (by simpa only [abs_of_neg hn] using hb.2.2.2.1) hy⟩

/-- The outgoing literal charged source as an inverse-cube coefficient
and its primitive; the identity is total, including the regular axis. -/
theorem em_curvature_source_j_eq_primitive (e : ℝ) (S : Fields) (u v : ℝ) :
    (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v)) =
    ((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 3) *
      ((∫ w in u..v, emPrimitiveOut e S u w) +
        2 * starRingEnd ℂ (∫ w in u..v, emPrimitiveOut e S u w)) := by
  by_cases hr : S.r u v = 0
  · simp [curvEM, hr]
  have hrc := ofReal_ne_zero.mpr hr
  simp only [curvEM, emPrimitiveOut, map_mul, map_inv₀, conj_ofReal]
  field_simp

/-- The incoming literal charged source as its negatively oriented
inverse-cube coefficient and charged primitive, including the axis. -/
theorem em_curvature_source_k_eq_primitive (e : ℝ) (S : Fields) (u v : ℝ) :
    (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      (curvEMIn e S u v + 2 * starRingEnd ℂ (curvEMIn e S u v)) =
    (-(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 3) *
      ((∫ w in u..v, emPrimitiveIn e S w v) +
        2 * starRingEnd ℂ (∫ w in u..v, emPrimitiveIn e S w v)) := by
  by_cases hr : S.r u v = 0
  · simp [curvEMIn, hr]
  have hrc := ofReal_ne_zero.mpr hr
  simp only [curvEMIn, emPrimitiveIn, map_neg, map_mul, map_inv₀, conj_ofReal]
  field_simp
  ; ring

end EmcsfAcExtension.Local.Stab
