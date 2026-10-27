module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.ChargePrimitive
import EmcsfAcExtension.Local.Apriori.ChargeSource
import EmcsfAcExtension.Local.Calculus.CurvatureIntegral

/-! # Splitting scalar and electric characteristic forcing

The two curvature representations have different oriented primitives. After
this distinction is retained, the electric error has a pointwise bound with
the scalar variation as a factor (`charged_SF_new_version.tex:L4647–L4668`).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

private theorem norm_curvature_sum (m C : ℂ) :
    ‖m * (C + 2 * starRingEnd ℂ C)‖ ≤ 3 * ‖m * C‖ := by
  have hc : ‖C + 2 * starRingEnd ℂ C‖ ≤ 3 * ‖C‖ := by
    calc
      _ ≤ ‖C‖ + ‖(2 : ℂ)‖ * ‖starRingEnd ℂ C‖ := by
        simpa only [norm_mul] using norm_add_le C (2 * starRingEnd ℂ C)
      _ = _ := by simp; ring
  rw [norm_mul, norm_mul]
  have hm := mul_le_mul_of_nonneg_left hc (norm_nonneg m)
  nlinarith only [hm]

private theorem norm_split_forcing (m Cs Ce E : ℂ) :
    ‖m * ((Cs + Ce) + 2 * starRingEnd ℂ (Cs + Ce)) + E‖ ≤
      3 * ‖m * Cs‖ + ‖m * (Ce + 2 * starRingEnd ℂ Ce)‖ + ‖E‖ := by
  have he : m * ((Cs + Ce) + 2 * starRingEnd ℂ (Cs + Ce)) + E =
      (m * (Cs + 2 * starRingEnd ℂ Cs) + m * (Ce + 2 * starRingEnd ℂ Ce)) + E := by
    rw [map_add]
    ring
  rw [he]
  calc
    _ ≤ ‖m * (Cs + 2 * starRingEnd ℂ Cs) + m * (Ce + 2 * starRingEnd ℂ Ce)‖ + ‖E‖ :=
      norm_add_le _ _
    _ ≤ (‖m * (Cs + 2 * starRingEnd ℂ Cs)‖ +
        ‖m * (Ce + 2 * starRingEnd ℂ Ce)‖) + ‖E‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add (norm_curvature_sum m Cs) le_rfl) le_rfl

private theorem electric_curvature_multiplier {c d r ε B : ℝ} {z D : ℂ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hd : 0 ≤ d) (_hB : 0 ≤ B)
    (hz : ‖z‖ ≤ 4 * ε * d) (hD : ‖D‖ ≤ B * r ^ 2) :
    ‖((c : ℂ) * z / (r : ℂ) ^ 2) * (D + 2 * starRingEnd ℂ D)‖ ≤
      12 * B * ε * |c| * d := by
  apply (norm_curvature_sum ((c : ℂ) * z / (r : ℂ) ^ 2) D).trans
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  calc
    _ ≤ 3 * (|c| * (4 * ε * d) / r ^ 2 * (B * r ^ 2)) := by gcongr
    _ = _ := by field_simp; ring

/-- Both full characteristic forcing fields are bounded by three times
their respective scalar primitive density and an electric density of size
`C e² M² ε (-ν)λ`. The same universal `C` is chosen before all data;
it depends only on the fixed box, uniformly in higher derivatives. -/
theorem characteristic_forcing_scalar_majorants :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 →
    ∀ u v, (u, v) ∈ triangle 0 s →
      (‖S.nu u v * S.theta u v / S.r u v ^ 2 *
          (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ ≤
        3 * ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
          curvScalar (triangle 0 s) S u v‖ +
        C * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v) ∧
      (‖S.lam u v * S.xi u v / S.r u v ^ 2 *
          (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ ≤
        3 * ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
          curvScalarIn e (triangle 0 s) S u v‖ +
        C * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v) := by
  obtain ⟨Co, hCo, hco⟩ := bv_c_charge
  obtain ⟨Ci, hCi, hci⟩ := Area.incoming_curvature_charge
  obtain ⟨Cd, hCd, hsource⟩ := bv_e_bounds
  refine ⟨Cd + 12 * (Co + Ci), by positivity, ?_⟩
  intro e s ε M S h hset hε u v hp
  have hε0 := hset.eps_nonneg
  have hn := (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le
  have hl := (hset.c1.lam_pos (u, v) hp).le
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε0]
  rcases eq_or_lt_of_le hp.2.1 with heq | huv
  · change u = v at heq
    subst v
    have hr := (hset.c1.axis u hp).1
    simp only [emSourceJ, emSourceK, hr, Complex.ofReal_zero,
      zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul, mul_zero, add_zero, norm_zero]
    constructor <;> positivity
  · have hr := hset.c1.r_pos (u, v) hp huv
    have hB : 0 ≤ (Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2 := by positivity
    have hco' : ‖curvEM e S u v‖ ≤
        ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 :=
      (hco e s ε M S h hset u v hp.1 huv hp.2.2).trans (by
        gcongr
        exact le_add_of_nonneg_right hCi.le)
    have hci' : ‖curvEMIn e S u v‖ ≤
        ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * S.r u v ^ 2 := by
      have hi := hci e s ε M S h hset u v hp.1 huv hp.2.2
      simpa only [curvEMIn, norm_neg] using hi.trans (by
        gcongr
        exact le_add_of_nonneg_left hCo.le)
    have ej := electric_curvature_multiplier hr hε0 hl hB
      (hset.theta_norm_le hp) hco' (c := S.nu u v)
    have ek := electric_curvature_multiplier hr hε0 hn hB
      (hset.xi_norm_le hp) hci' (c := S.lam u v)
    rw [abs_of_neg (hset.c1.nu_neg (u, v) hp)] at ej
    rw [abs_of_pos (hset.c1.lam_pos (u, v) hp)] at ek
    have hb : 12 * ((Co + Ci) * e ^ 2 * M ^ 2 * ε ^ 2) * ε *
        (-S.nu u v) * S.lam u v ≤
        12 * (Co + Ci) * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
      have hi := mul_le_mul_of_nonneg_left hε2
        (show 0 ≤ 12 * (Co + Ci) * e ^ 2 * M ^ 2 * ε *
          (-S.nu u v) * S.lam u v by positivity)
      nlinarith only [hi]
    have ej' := ej.trans hb
    have ek' : ‖(S.lam u v * S.xi u v / S.r u v ^ 2) *
        (curvEMIn e S u v + 2 * starRingEnd ℂ (curvEMIn e S u v))‖ ≤
        12 * (Co + Ci) * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
      apply ek.trans
      convert hb using 1
      ring
    have hd := hsource e s ε M S h hset hε u v hp.1 huv hp.2.2
    have hdj := (le_add_of_nonneg_right (norm_nonneg (emSourceK e S u v))).trans hd
    have hdk := (le_add_of_nonneg_left (norm_nonneg (emSourceJ e S u v))).trans hd
    constructor
    · rw [Stab.curvature_radial_representation hset.c1 hp.1 huv hp.2.2]
      have hi := norm_split_forcing (S.nu u v * S.theta u v / S.r u v ^ 2)
        (curvScalar (triangle 0 s) S u v) (curvEM e S u v) (emSourceJ e S u v)
      nlinarith only [hi, ej', hdj]
    · have hc : starRingEnd ℂ (curv S u v) =
          curvScalarIn e (triangle 0 s) S u v + curvEMIn e S u v :=
        Stab.curvature_radial_representation_in hset.c1 hp.1 huv hp.2.2
      have hcc : curv S u v = starRingEnd ℂ
          (curvScalarIn e (triangle 0 s) S u v + curvEMIn e S u v) := by
        rw [← hc]
        simp
      rw [hc, hcc]
      have hi := norm_split_forcing (S.lam u v * S.xi u v / S.r u v ^ 2)
        (curvScalarIn e (triangle 0 s) S u v) (curvEMIn e S u v) (emSourceK e S u v)
      nlinarith only [hi, ek', hdk]

end EmcsfAcExtension.Local
