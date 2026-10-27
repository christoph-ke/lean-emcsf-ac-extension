module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.AreaTransport
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.ChargePrimitive
import EmcsfAcExtension.Local.Apriori.ChargeSource

/-! # Homogeneous and electromagnetic sup budgets

The incoming homogeneous exponent and the electric source in the outgoing
renormalized transport are bounded before taking a supremum. Constants are
universal in the standing box, as in `charged_SF_new_version.tex:L6233–6233`.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem curvature_multiplier_aux {c r ε B : ℝ} {z D : ℂ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hc : |c| ≤ 1)
    (hz : ‖z‖ ≤ 4 * ε) (hD : ‖D‖ ≤ B * r ^ 2) (_hB : 0 ≤ B) :
    ‖((c : ℂ) * z / (r : ℂ) ^ 2) * (D + 2 * starRingEnd ℂ D)‖ ≤
      12 * B * ε := by
  have hs : ‖D + 2 * starRingEnd ℂ D‖ ≤ 3 * (B * r ^ 2) := by
    calc
      _ ≤ ‖D‖ + ‖(2 : ℂ)‖ * ‖starRingEnd ℂ D‖ := by
        simpa only [norm_mul] using norm_add_le D (2 * starRingEnd ℂ D)
      _ = 3 * ‖D‖ := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by norm_num)
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  calc
    _ ≤ (1 * (4 * ε) / r ^ 2) * (3 * (B * r ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

/-- The direct and outgoing electric-curvature sources have a universal
pointwise bound `C e² M² ε`. `C` is independent of `e,T,M,h,S` and all
initial derivative norms. The threshold `ε ≤ 1` absorbs the cubic error. -/
theorem smooth_em_source_bound_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ 1 → ∀ u v,
      0 ≤ u → u < v → v ≤ T →
      ‖emSourceJ e S u v‖ +
        ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
          (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ ≤
        C * e ^ 2 * M ^ 2 * ε := by
  obtain ⟨C, hC, hsource⟩ := bv_e_bounds
  obtain ⟨D, hD, hcurv⟩ := bv_c_charge
  refine ⟨C + 12 * D, by positivity, ?_⟩
  intro e T ε M S h hset hε u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hε0 := hset.eps_nonneg
  have hb := hset.box (u, v) hp
  have hn : |S.nu u v| ≤ 1 := by
    rw [abs_of_neg (hset.c1.nu_neg _ hp)]
    exact hb.2.2.2.1
  have hθ : ‖S.theta u v‖ ≤ 4 * ε :=
    (hset.theta_norm_le hp).trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hb.2.1 (by positivity : 0 ≤ 4 * ε))
  have he := (le_add_of_nonneg_right (norm_nonneg (emSourceK e S u v))).trans
    (hsource e T ε M S h hset hε u v hu huv hvT)
  have hgeom : (-S.nu u v) * S.lam u v ≤ 1 := by
    exact (mul_le_mul hb.2.2.2.1 hb.2.1 (hset.c1.lam_pos _ hp).le
      (by norm_num)).trans_eq (one_mul _)
  have he' : ‖emSourceJ e S u v‖ ≤ C * e ^ 2 * M ^ 2 * ε := by
    apply he.trans
    simpa only [mul_assoc, mul_one] using
      mul_le_mul_of_nonneg_left hgeom (by positivity : 0 ≤ C * e ^ 2 * M ^ 2 * ε)
  have hc := curvature_multiplier_aux (hset.c1.r_pos _ hp huv) hε0 hn hθ
    (hcurv e T ε M S h hset u v hu huv hvT)
    (show 0 ≤ D * e ^ 2 * M ^ 2 * ε ^ 2 by positivity)
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε0]
  have hc' :
      ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
        (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ ≤
        12 * D * e ^ 2 * M ^ 2 * ε := by
    apply hc.trans
    have hi := mul_le_mul_of_nonneg_left hε2
      (show 0 ≤ 12 * D * e ^ 2 * M ^ 2 * ε by positivity)
    nlinarith only [hi]
  calc
    _ ≤ C * e ^ 2 * M ^ 2 * ε + 12 * D * e ^ 2 * M ^ 2 * ε := add_le_add he' hc'
    _ = _ := by ring

/-- [node restart-sec-independent-null-construction#homogeneous-em-sup]
The homogeneous exponent is at most `C ε ‖K‖₁`, and the unamplified electric
forcing on any incoming segment is at most `C e² M² T ε`
(`charged_SF_new_version.tex:L6233–6233`). `C` is universal: independent of all data,
parameters, and derivative norms. The integral conclusion uses a nonnegative
integral, so it also certifies finiteness without an integrability premise. -/
theorem Null.homogeneous_em_sup :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ 1 / 8 →
      (∀ v ∈ Icc 0 T, ∀ a b, 0 ≤ a → a ≤ b → b ≤ v →
        (∫ u in a..b, -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) ≤
          C * ε * ∫ u in 0..T, (inEnv T (kC1 e (triangle 0 T) S) u).toReal) ∧
      (∀ u v, 0 ≤ u → u < v → v ≤ T →
        ‖emSourceJ e S u v‖ +
          ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
            (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ ≤
          C * e ^ 2 * M ^ 2 * ε) ∧
      (∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
        (∫⁻ a in Icc 0 u, ‖emSourceJ e S a v‖ₑ +
          ‖(S.nu a v * S.theta a v / S.r a v ^ 2) *
            (curvEM e S a v + 2 * starRingEnd ℂ (curvEM e S a v))‖ₑ) ≤
          ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε)) := by
  obtain ⟨A, hA, hhom⟩ := Area.homogeneous_transport_bounds
  obtain ⟨B, hB, hem⟩ := smooth_em_source_bound_aux
  refine ⟨A + B, by positivity, ?_⟩
  intro e T ε M S h hset hε
  have hε0 := hset.eps_nonneg
  have hε1 : ε ≤ 1 := hε.trans (by norm_num)
  have hAB : B ≤ A + B := le_add_of_nonneg_left hA.le
  have hb (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
      ‖emSourceJ e S u v‖ +
        ‖(S.nu u v * S.theta u v / S.r u v ^ 2) *
          (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))‖ ≤
        (A + B) * e ^ 2 * M ^ 2 * ε :=
    (hem e T ε M S h hset hε1 u v hu huv hvT).trans (by gcongr)
  refine ⟨?_, hb, ?_⟩
  · intro v hv a b ha hab hb
    have hh := Real.exp_le_exp.mp ((hhom e T ε M S h hset hε).1 v hv a b ha hab hb)
    apply hh.trans
    have hi : 0 ≤ ∫ u in 0..T, (inEnv T (kC1 e (triangle 0 T) S) u).toReal :=
      intervalIntegral.integral_nonneg hset.pos.le (fun _ _ => ENNReal.toReal_nonneg)
    gcongr
    exact le_add_of_nonneg_right hB.le
  · intro u v hu huv hvT
    calc
      _ ≤ ∫⁻ _a in Icc 0 u, ENNReal.ofReal ((A + B) * e ^ 2 * M ^ 2 * ε) := by
        apply lintegral_mono_ae
        have hne : ∀ᵐ a ∂volume.restrict (Icc 0 u), a ≠ v :=
          ae_restrict_of_ae (by simp [ae_iff])
        filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with a ha hav
        rw [← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (hb a v ha.1
          (lt_of_le_of_ne (ha.2.trans huv) hav) hvT)
      _ = ENNReal.ofReal (((A + B) * e ^ 2 * M ^ 2 * ε) * u) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]
        exact (ENNReal.ofReal_mul
          (by positivity : 0 ≤ (A + B) * e ^ 2 * M ^ 2 * ε)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hi := mul_le_mul_of_nonneg_left (huv.trans hvT)
          (show 0 ≤ (A + B) * e ^ 2 * M ^ 2 * ε by positivity)
        nlinarith only [hi]

end EmcsfAcExtension.Local
