module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeRegular
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeScalar
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeEM
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourceAux
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.CurvatureIntegral
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Absolute area budget for the common geometric source

The curvature decomposition splits the common real source into its scalar
primitive part and the electric part. The inverse gap costs only a box
constant (`charged_SF_new_version.tex:L4878–L4885`).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- The geometric source's absolute value has a measurable zero extension
from the triangle. Its literal axis value is zero; no continuity or
integrability of the source at that axis is assumed. -/
theorem measurable_geometric_source {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    Measurable ((triangle 0 T).indicator (fun p => ‖geomSource S p.1 p.2‖ₑ)) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => (geomSource S p.1 p.2 : ℂ))
      (triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
    Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_geomSource_off_axis hT hS)
  have hm := measurable_triangle_enorm_of_zero_axis hc (by
    intro t ht
    simp [geomSource, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1])
  have heq : (fun p : ℝ × ℝ => ‖(geomSource S p.1 p.2 : ℂ)‖ₑ) =
      fun p => ‖geomSource S p.1 p.2‖ₑ := by
    funext p
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  rwa [heq] at hm

private theorem scalar_primitive_continuous {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (curvScalar (triangle 0 T) S))
      (triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}) := by
  let D := triangle 0 T
  let O := D ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := Complex.continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn
  have cn := Complex.continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn
  have cz := hS.c1_xi.continuousOn.div cn
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)
  let F := fun u v => (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) * jC1 D S u v
  have cF : ContinuousOn (Function.uncurry F) D :=
    (cr.mul cz.star).mul (continuousOn_jC1_aux hT hS)
  have cp := continuousOn_integral_outgoing cF
  have hr (p : ℝ × ℝ) (hp : p ∈ O) : (S.r p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.r_pos p hp.1 hp.2).ne'
  have cri := (continuousOn_const (c := (1 : ℂ))).div
    (cr.mono (show O ⊆ D from inter_subset_left)) hr
  apply (cri.mul (cp.mono (show O ⊆ D from inter_subset_left))).congr
  intro p hp
  change curvScalar D S p.1 p.2 =
    (1 : ℂ) / S.r p.1 p.2 * ∫ x in p.1..p.2, F p.1 x
  simp only [curvScalar, F, D, one_div]

private theorem split_densities_measurable {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) :
    Measurable ((triangle 0 T).indicator (fun p : ℝ × ℝ =>
      ‖S.nu p.1 p.2 * (S.lam p.1 p.2 : ℂ) / S.r p.1 p.2 ^ 2 *
        curvScalar (triangle 0 T) S p.1 p.2‖ₑ)) ∧
    Measurable ((triangle 0 T).indicator (fun p : ℝ × ℝ =>
      ENNReal.ofReal (|-2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
        ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2) *
          ((curvEM e S p.1 p.2).re - 2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2)|))) := by
  let O := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cCs := scalar_primitive_continuous hset.pos hset.c1
  have cCe : ContinuousOn (Function.uncurry (curvEM e S)) O := by
    apply ((continuousOn_curv_aux hset.pos hset.c1).mono inter_subset_left).sub cCs |>.congr
    intro p hp
    change curvEM e S p.1 p.2 = curv S p.1 p.2 - curvScalar (triangle 0 T) S p.1 p.2
    rw [Stab.curvature_radial_representation hset.c1 hp.1.1 hp.2 hp.1.2.2]
    abel
  have cr := hset.c1.c1_r.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cn := hset.c1.c1_nu.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cl := hset.c1.c1_lam.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cq := hset.c1.c1_Q.continuousOn.mono (show O ⊆ triangle 0 T from inter_subset_left)
  have cH : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) O :=
    (continuousOn_const (c := (1 : ℝ))).sub
    ((continuousOn_mu_aux hset.pos hset.c1).mono inter_subset_left)
  have hr (p : ℝ × ℝ) (hp : p ∈ O) := (hset.c1.r_pos p hp.1 hp.2).ne'
  have hH (p : ℝ × ℝ) (hp : p ∈ O) := (hset.c1.one_sub_mu_pos p hp.1).ne'
  have crc := Complex.continuous_ofReal.comp_continuousOn cr
  have cnc := Complex.continuous_ofReal.comp_continuousOn cn
  have clc := Complex.continuous_ofReal.comp_continuousOn cl
  have cA : ContinuousOn (fun p : ℝ × ℝ => -2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
      ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2)) O :=
    (((cn.const_mul (-2)).mul cl).div (cH.mul (cr.pow 2))
    (fun p hp => mul_ne_zero (hH p hp) (pow_ne_zero 2 (hr p hp))))
  have cB : ContinuousOn (fun p : ℝ × ℝ => (curvEM e S p.1 p.2).re -
      2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) O :=
    (Complex.continuous_re.comp_continuousOn cCe).sub
    ((((cq.pow 2).const_mul 2).div (cr.pow 2) (fun p hp => pow_ne_zero 2 (hr p hp))))
  constructor
  · apply measurable_triangle_enorm_of_zero_axis
      ((((cnc.mul clc).div (crc.pow 2)
        (fun p hp => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hr p hp)))).mul cCs))
    intro t ht
    simp [(hset.c1.axis t ⟨ht.1, le_rfl, ht.2⟩).1]
  · have hm := measurable_triangle_enorm_of_zero_axis
      (Complex.continuous_ofReal.comp_continuousOn (cA.mul cB)) (by
        intro t ht
        simp [(hset.c1.axis t ⟨ht.1, le_rfl, ht.2⟩).1])
    have heq : (fun p : ℝ × ℝ => ‖(((-2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
        ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2)) *
          ((curvEM e S p.1 p.2).re - 2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) : ℝ) : ℂ)‖ₑ) =
        fun p => ENNReal.ofReal (|-2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
          ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2) *
            ((curvEM e S p.1 p.2).re - 2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2)|) := by
      funext p
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    change Measurable ((triangle 0 T).indicator (fun p =>
      ‖(((-2 * S.nu p.1 p.2 * S.lam p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2)) *
        ((curvEM e S p.1 p.2).re - 2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) : ℝ) : ℂ)‖ₑ)) at hm
    rwa [heq] at hm

private theorem geometric_split_area_bound {e T ε M X Y : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h)
    (hs : (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar (triangle 0 T) S u v‖ₑ) ≤
      ENNReal.ofReal X)
    (he : (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
        ((1 - S.mu u v) * S.r u v ^ 2) *
          ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|)) ≤ ENNReal.ofReal Y) :
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ENNReal.ofReal 4 * ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 *
        curvScalar (triangle 0 T) S u v‖ₑ +
      ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
        ((1 - S.mu u v) * S.r u v ^ 2) *
          ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|)) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal X + ENNReal.ofReal Y := by
  classical
  let D := triangle 0 T
  let G := fun p : ℝ × ℝ => ‖S.nu p.1 p.2 * (S.lam p.1 p.2 : ℂ) / S.r p.1 p.2 ^ 2 *
    curvScalar D S p.1 p.2‖ₑ
  let E := fun p : ℝ × ℝ => ENNReal.ofReal (|-2 * S.nu p.1 p.2 * S.lam p.1 p.2 /
    ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2) *
      ((curvEM e S p.1 p.2).re - 2 * S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2)|)
  obtain ⟨hG, hE⟩ := split_densities_measurable hset
  have hsum : Measurable (D.indicator (fun p => ENNReal.ofReal 4 * G p + E p)) := by
    convert (hG.const_mul (ENNReal.ofReal 4)).add hE using 1
    funext p
    by_cases hp : p ∈ D <;> simp [hp, G, E, D]
  rw [← (triangle_lintegral_orders hsum).1]
  have hid : (∫⁻ p in D, ENNReal.ofReal 4 * G p + E p ∂(volume.prod volume)) =
      ENNReal.ofReal 4 * (∫⁻ p in D, G p ∂(volume.prod volume)) +
        ∫⁻ p in D, E p ∂(volume.prod volume) := by
    calc
      _ = ∫⁻ p in D, ENNReal.ofReal 4 * D.indicator G p + D.indicator E p
          ∂(volume.prod volume) := setLIntegral_congr_fun (measurableSet_triangle 0 T)
            (fun p hp => by rw [indicator_of_mem hp, indicator_of_mem hp])
      _ = _ := by
        rw [lintegral_add_left (hG.const_mul (ENNReal.ofReal 4)),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        change ENNReal.ofReal 4 * (∫⁻ p in D, D.indicator G p ∂(volume.prod volume)) +
          (∫⁻ p in D, D.indicator E p ∂(volume.prod volume)) = _
        simp only [setLIntegral_indicator (measurableSet_triangle 0 T), D, inter_self]
  rw [hid, (triangle_lintegral_orders hG).1, (triangle_lintegral_orders hE).1]
  exact add_le_add (mul_le_mul' le_rfl hs) he

private theorem geometric_source_split_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    ‖geomSource S u v‖ₑ ≤ ENNReal.ofReal 4 *
        ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar (triangle 0 T) S u v‖ₑ +
      ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
        ((1 - S.mu u v) * S.r u v ^ 2) *
          ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|) := by
  rcases eq_or_lt_of_le hp.2.1 with huv | huv
  · change u = v at huv
    subst v
    simp [geomSource, (hset.c1.axis u hp).1]
  have hr := hset.c1.r_pos (u, v) hp huv
  have hn := hset.c1.nu_neg (u, v) hp
  have hl := hset.c1.lam_pos (u, v) hp
  have hH := hset.c1.one_sub_mu_pos (u, v) hp
  let A := -(2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2))
  have hnn : 0 ≤ -S.nu u v := (neg_pos.mpr hn).le
  have hll : 0 ≤ S.lam u v := hl.le
  have hA : 0 ≤ A := by
    have hid : A = 2 * (-S.nu u v) * S.lam u v /
        ((1 - S.mu u v) * S.r u v ^ 2) := by dsimp only [A]; ring
    rw [hid]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hnn) hll)
      (mul_nonneg hH.le (sq_nonneg _))
  have hgap : 2 / (1 - S.mu u v) ≤ 4 := by
    apply (div_le_iff₀ hH).mpr
    linarith only [(hset.box (u, v) hp).2.2.2.2.1]
  have hfactor : A ≤ 4 * ((-S.nu u v) * S.lam u v / S.r u v ^ 2) := by
    calc
      A = (2 / (1 - S.mu u v)) * ((-S.nu u v) * S.lam u v / S.r u v ^ 2) := by
        dsimp only [A]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap
        (div_nonneg (mul_nonneg hnn hll) (sq_nonneg _))
  have hnorm : ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 *
      curvScalar (triangle 0 T) S u v‖ =
      ((-S.nu u v) * S.lam u v / S.r u v ^ 2) * ‖curvScalar (triangle 0 T) S u v‖ := by
    simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg hn, abs_of_pos hl, abs_of_pos hr]
  have hb : |geomSource S u v| ≤ 4 *
        ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar (triangle 0 T) S u v‖ +
      |A * ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)| := by
    rw [geomSource, Stab.curvature_radial_representation hset.c1 hp.1 huv hp.2.2,
      Complex.add_re]
    change |A * ((curvScalar (triangle 0 T) S u v).re + (curvEM e S u v).re -
      2 * (S.Q u v ^ 2 / S.r u v ^ 2))| ≤ _
    have hid : A * ((curvScalar (triangle 0 T) S u v).re + (curvEM e S u v).re -
        2 * (S.Q u v ^ 2 / S.r u v ^ 2)) =
        A * (curvScalar (triangle 0 T) S u v).re +
          A * ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2) := by ring
    rw [hid, hnorm]
    apply (abs_add_le _ _).trans
    apply add_le_add _ le_rfl
    rw [abs_mul, abs_of_nonneg hA]
    calc
      _ ≤ A * ‖curvScalar (triangle 0 T) S u v‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hA
      _ ≤ _ := by
        have hi := mul_le_mul_of_nonneg_right hfactor
          (norm_nonneg (curvScalar (triangle 0 T) S u v))
        nlinarith only [hi]
  rw [← ofReal_norm, Real.norm_eq_abs]
  apply (ENNReal.ofReal_le_ofReal hb).trans_eq
  rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) (norm_nonneg _)) (abs_nonneg _),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ofReal_norm]
  congr 3
  dsimp only [A]
  ring

/-- The common geometric source has an absolute `C ε²` area budget in
both null integration orders. The positive thresholds and `C` precede all
data and depend only on the fixed box, uniformly in higher derivatives. -/
theorem geometric_source_area : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S u v‖ₑ) ≤
        ENNReal.ofReal (C * ε ^ 2) ∧
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖geomSource S u v‖ₑ) ≤
        ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨ε₀, δ₁, Cs, hε₀, hδ₁, hCs, hscalar⟩ := scalar_geometric_area
  obtain ⟨Ce, hCe, helectric⟩ := electromagnetic_geometric_area
  refine ⟨ε₀, min δ₁ 1, 4 * Cs + Ce, hε₀, lt_min hδ₁ (by norm_num), by positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have hs := (hscalar e T ε M S h hset hε (hδ.trans (min_le_left _ _))).2
  have he := (helectric e T ε M S h hset).1
  have hd0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; have := hset.one_le_M; positivity
  have hd2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by
    nlinarith only [hd0, hδ.trans (min_le_right δ₁ 1)]
  have horders := swap_triangle_lintegral_of_measurable_extension
    (measurable_geometric_source hset.pos hset.c1)
  have hout : (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S u v‖ₑ) ≤
      ENNReal.ofReal ((4 * Cs + Ce) * ε ^ 2) := by
    calc
      _ ≤ ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
          ENNReal.ofReal 4 * ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 *
            curvScalar (triangle 0 T) S u v‖ₑ +
          ENNReal.ofReal (|-2 * S.nu u v * S.lam u v /
            ((1 - S.mu u v) * S.r u v ^ 2) *
              ((curvEM e S u v).re - 2 * S.Q u v ^ 2 / S.r u v ^ 2)|) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro u hu
        apply setLIntegral_mono' measurableSet_Icc
        intro v hv
        exact geometric_source_split_bound hset ⟨hu.1, hv.1, hv.2⟩
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Cs * ε ^ 2) +
          ENNReal.ofReal (Ce * (|e| * (T / 2) * M) ^ 2 * ε ^ 2) := by
        exact geometric_split_area_bound hset hs he
      _ ≤ _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hi := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hCe.le (sq_nonneg ε))
        nlinarith only [hi]
  exact ⟨hout, horders ▸ hout⟩

end EmcsfAcExtension.Local
