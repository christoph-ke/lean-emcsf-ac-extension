module

public import EmcsfAcExtension.Global.Observation.WrappersExact
import Mathlib

/-! # Separate neutral and electromagnetic wave sources

The components are bounded before addition, so cancellation in the full
source cannot hide an omitted estimate. Source: charged_SF_new_version.tex:L2440–2461.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] Separate component bounds and exact neutral/electric splitting.
`Cn` depends only on `K`; `Ce` additionally depends on `Cp,B`. Every constant
precedes all fields, scales, amplitudes, couplings and errors. The source
consumer derives all bounds used here from the actual normalization record. -/
theorem outer_source_components_of_bounds (K Cp : ℝ) (hK : 1 ≤ K) (hCp : 0 ≤ Cp) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ B : ℝ, 0 ≤ B →
      ∃ Ce : ℝ, 0 < Ce ∧
        ∀ (r L m mStar Q qStar e eta A a lam Nphi Nm : ℝ)
          (H psi w yStar fPrime : ℂ),
          1 ≤ r → 0 < L → 0 ≤ eta →
          |m| ≤ 2 → 1 / 2 ≤ 1 - 2 * m / r → 1 / 2 ≤ 1 - 2 * mStar / r →
          a ∈ Icc 0 1 → lam ∈ Icc 0 1 →
          |Q| ≤ 2 → |qStar| ≤ 1 → |Q - qStar| ≤ B * eta →
          |e| * L * (1 + ‖H‖) = eta →
          |e * A| * (1 + ‖H‖) ≤ Cp * eta / (L * r) →
          ‖w‖ ≤ Nphi → |m - mStar| ≤ Nm →
          ‖psi‖ ≤ K → ‖yStar‖ ≤ K / r → ‖fPrime‖ ≤ K / r ^ 2 →
          let k := (2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)
          let kStar : ℝ := (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)
          let kq := (2 * m / r - qStar ^ 2 / r ^ 2) / (1 - 2 * m / r)
          let neutral := -((a * k / r ^ 2 : ℝ) : ℂ) * w +
            ((a / r : ℝ) : ℂ) * yStar * ((kq - kStar : ℝ) : ℂ)
          let electricQ := -((a / r : ℝ) : ℂ) * yStar *
            (((Q ^ 2 - qStar ^ 2) / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ)
          ‖neutral‖ ≤ Cn * (Nphi + Nm) / r ^ 3 ∧
          ‖electricQ - I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime) +
            I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
              (psi + (r : ℂ) * H)‖ ≤ Ce * (eta / r ^ 4 + eta / (L * r)) ∧
          ‖electricQ‖ ≤ Ce * eta / r ^ 4 ∧
          |Q ^ 2 - qStar ^ 2| / r ^ 4 ≤ Ce * eta / r ^ 4 ∧
          ‖I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime)‖ ≤ Ce * eta / (L * r) ∧
          ‖I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
            (psi + (r : ℂ) * H)‖ ≤ Ce * eta / (L * r) ∧
          -((a * k / r ^ 2 : ℝ) : ℂ) * w +
            ((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ) = neutral + electricQ := by
  refine ⟨16 * K, by positivity, fun B hB =>
    ⟨(6 * B + Cp + 4) * K, by positivity, ?_⟩⟩
  intro r L m mStar Q qStar e eta A a lam Nphi Nm H psi w yStar fPrime
    hr hL heta hm hg hgs ha hlam hQ hq hcharge hscale hpotential hw hmass hpsi hy hf
  let k := (2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)
  let kStar := (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hgp : 0 < 1 - 2 * m / r := by linarith only [hg]
  have hgsPos : 0 < 1 - 2 * mStar / r := by linarith only [hgs]
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hNphi : 0 ≤ Nphi := (norm_nonneg _).trans hw
  have hNm : 0 ≤ Nm := (abs_nonneg _).trans hmass
  have hk : |k| ≤ 16 / r := outer_geometric_coefficient_bound hr hm hQ hg
  have hkk : |k - kStar| ≤ 16 * Nm / r + 6 * B * eta / r ^ 2 :=
    outer_geometric_difference_bound hr hg hgs hmass hQ hq hcharge
  have hfirst : ‖-((a * k / r ^ 2 : ℝ) : ℂ) * w‖ ≤ 16 * Nphi / r ^ 3 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_of_nonneg ha.1, abs_of_pos (sq_pos_of_pos hrp)]
    calc
      _ ≤ ((1 * (16 / r)) / r ^ 2) * Nphi := by gcongr; exact ha.2
      _ = _ := by ring
  have hsecond : ‖((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ)‖ ≤
      16 * K * Nm / r ^ 3 + 6 * K * B * eta / r ^ 4 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_nonneg ha.1, abs_of_pos hrp]
    calc
      _ ≤ (1 / r) * (K / r) * (16 * Nm / r + 6 * B * eta / r ^ 2) := by
        gcongr; exact ha.2
      _ = _ := by ring
  have hfK : ‖fPrime‖ ≤ K := by
    apply hf.trans
    apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
    have hr2 : 1 ≤ r ^ 2 := by nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr), hr]
    nlinarith only [mul_nonneg hK0 (sub_nonneg.mpr hr2)]
  have hHf : ‖H + fPrime‖ ≤ K * (1 + ‖H‖) := by
    apply (norm_add_le _ _).trans
    have hprod := mul_nonneg (sub_nonneg.mpr hK) (norm_nonneg H)
    nlinarith only [hfK, hprod]
  have hthird : ‖I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime)‖ ≤
      Cp * K * eta / (L * r) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hlam.1]
    calc
      _ ≤ |e * A| * 1 * (K * (1 + ‖H‖)) := by gcongr; exact hlam.2
      _ = K * (|e * A| * (1 + ‖H‖)) := by ring
      _ ≤ K * (Cp * eta / (L * r)) := mul_le_mul_of_nonneg_left hpotential hK0
      _ = _ := by ring
  have hcoeff : |e * a * Q / ((1 - 2 * m / r) * r ^ 2)| ≤ 4 * |e| / r ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg ha.1,
      abs_of_pos (mul_pos hgp (sq_pos_of_pos hrp))]
    apply (div_le_div_iff₀ (mul_pos hgp (sq_pos_of_pos hrp)) (sq_pos_of_pos hrp)).mpr
    have hnum : |e| * a * |Q| ≤ 2 * |e| := by
      calc
        _ ≤ |e| * 1 * 2 := by gcongr; exact ha.2
        _ = _ := by ring
    have hn := mul_le_mul_of_nonneg_right hnum (sq_nonneg r)
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4 * |e| * r ^ 2 by positivity)
    linear_combination hn + hg'
  have hpsiH : ‖psi + (r : ℂ) * H‖ ≤ K * r * (1 + ‖H‖) := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
    have hKr := mul_le_mul_of_nonneg_left hr hK0
    have hKH := mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hrp.le (norm_nonneg H))
    nlinarith only [hpsi, hKr, hKH]
  have hfourth : ‖I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
      (psi + (r : ℂ) * H)‖ ≤ 4 * K * eta / (L * r) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (4 * |e| / r ^ 2) * (K * r * (1 + ‖H‖)) :=
        mul_le_mul hcoeff hpsiH (norm_nonneg _) (by positivity)
      _ = 4 * K * eta / (L * r) := by rw [← hscale]; field_simp
  have hcharge2 : |Q ^ 2 - qStar ^ 2| ≤ 3 * B * eta := by
    rw [show Q ^ 2 - qStar ^ 2 = (Q - qStar) * (Q + qStar) by ring, abs_mul]
    have hsum : |Q + qStar| ≤ 3 := (abs_add_le _ _).trans (by linarith only [hQ, hq])
    exact (mul_le_mul hcharge hsum (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hCeQ : 6 * K * B ≤ (6 * B + Cp + 4) * K := by nlinarith only [hK0, mul_nonneg hK0 hCp]
  have hCeP : Cp * K ≤ (6 * B + Cp + 4) * K := by nlinarith only [hK0, mul_nonneg hK0 hB]
  have hCeF : 4 * K ≤ (6 * B + Cp + 4) * K :=
      by nlinarith only [mul_nonneg hK0 hB, mul_nonneg hK0 hCp]
  have hCe3 : 3 * B ≤ (6 * B + Cp + 4) * K := by
    nlinarith only [hK0, hB, mul_nonneg hK0 hCp, mul_nonneg hB (sub_nonneg.mpr hK)]
  have hmasspart : |(2 * m / r - qStar ^ 2 / r ^ 2) / (1 - 2 * m / r) - kStar| ≤ 16 * Nm / r := by
    have hh := outer_geometric_difference_bound (B := 0) (eta := 0) hr hg hgs hmass
      (hq.trans (by norm_num : (1 : ℝ) ≤ 2)) hq (by simp)
    simpa only [mul_zero, zero_mul, zero_div, add_zero] using hh
  have hnpart : ‖((a / r : ℝ) : ℂ) * yStar *
      (((2 * m / r - qStar ^ 2 / r ^ 2) / (1 - 2 * m / r) - kStar : ℝ) : ℂ)‖ ≤
        16 * K * Nm / r ^ 3 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_of_nonneg ha.1, abs_of_pos hrp]
    calc
      _ ≤ (1 / r) * (K / r) * (16 * Nm / r) := by gcongr; exact ha.2
      _ = _ := by ring
  have hepart : ‖-((a / r : ℝ) : ℂ) * yStar *
      (((Q ^ 2 - qStar ^ 2) / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ)‖ ≤
        6 * K * B * eta / r ^ 4 := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
      abs_of_nonneg ha.1, abs_of_pos hrp, abs_of_pos (mul_pos hgp (sq_pos_of_pos hrp))]
    calc
      _ ≤ (1 / r) * (K / r) * ((3 * B * eta) / ((1 / 2) * r ^ 2)) := by
        gcongr
        exact ha.2
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (norm_add_le _ _).trans ((add_le_add hfirst hnpart).trans ?_)
    have hh := mul_nonneg (sub_nonneg.mpr hK) hNphi
    linear_combination (16 / r ^ 3) * hh
  · apply ((norm_add_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add hepart hthird)) hfourth)).trans
    have hpos1 : 0 ≤ (Cp + 4) * K * eta / r ^ 4 := by positivity
    have hpos2 : 0 ≤ 6 * B * K * eta / (L * r) := by positivity
    linear_combination hpos1 + hpos2
  · exact hepart.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCeQ heta) (by positivity))
  · exact (div_le_div_of_nonneg_right hcharge2 (by positivity)).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCe3 heta) (by positivity))
  · exact hthird.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCeP heta) (by positivity))
  · exact hfourth.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCeF heta) (by positivity))
  · push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hgp.ne',
      Complex.ofReal_ne_zero.mpr hgsPos.ne', Complex.ofReal_ne_zero.mpr hrp.ne']
    ring

/-- [internal] The separated source inequalities at an actual comparison point.
This predicate only appears in conclusions. -/
@[expose] noncomputable def outerComponentsAt (Cn Ce : ℝ) (S : Fields) (H : ℂ) (phiStar yStar : ℝ →
    ℂ)
    (mStar : ℝ → ℝ) (qStar e eta L Nphi Nm u v : ℝ) : Prop :=
  let r := S.r u v
  let a := (-S.nu u v) * S.lam u v
  let g := 1 - S.mu u v
  let k := (S.mu u v - S.Q u v ^ 2 / r ^ 2) / g
  let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  let kq := (S.mu u v - qStar ^ 2 / r ^ 2) / g
  let neutral := -((a * k / r ^ 2 : ℝ) : ℂ) * scalarComparison S H phiStar u v +
    ((a / r : ℝ) : ℂ) * yStar r * ((kq - ks : ℝ) : ℂ)
  let electricQ := -((a / r : ℝ) : ℂ) * yStar r *
    (((S.Q u v ^ 2 - qStar ^ 2) / (g * r ^ 2) : ℝ) : ℂ)
  ‖neutral‖ ≤ Cn * (Nphi + Nm) / r ^ 3 ∧
    ‖electricQ - I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) *
      (H + (phiStar r + yStar r)) +
      I * ((e * a * S.Q u v / (g * r ^ 2) : ℝ) : ℂ) *
        (shiftedRphi S H u v + (r : ℂ) * H)‖ ≤ Ce * (eta / r ^ 4 + eta / (L * r)) ∧
    ‖electricQ‖ ≤ Ce * eta / r ^ 4 ∧
    |S.Q u v ^ 2 - qStar ^ 2| / r ^ 4 ≤ Ce * eta / r ^ 4 ∧
    ‖I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) *
      (H + (phiStar r + yStar r))‖ ≤ Ce * eta / (L * r) ∧
    ‖I * ((e * a * S.Q u v / (g * r ^ 2) : ℝ) : ℂ) *
      (shiftedRphi S H u v + (r : ℂ) * H)‖ ≤ Ce * eta / (L * r) ∧
    -((a * k / r ^ 2 : ℝ) : ℂ) * scalarComparison S H phiStar u v +
      ((a / r : ℝ) : ℂ) * yStar r * ((k - ks : ℝ) : ℂ) = neutral + electricQ

/-- [internal] Specialize all separated components to the normalized fields.
The only estimate inputs are discharged by the stopped-region consumer.
The neutral coefficient depends only on `Kstatic`; the electric coefficient
also depends on the prior potential and charge coefficients. -/
theorem outer_components_of_normalization (Kstatic Cp : ℝ) (hK : 0 ≤ Kstatic) (hCp : 0 ≤ Cp) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ B : ℝ, 0 ≤ B → ∃ Ce : ℝ, 0 < Ce ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e Nphi Nm Bboundary Ct : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e → 1 ≤ Lzero →
    comparisonNorm R (scalarComparison S H phiStar) ≤ 1 →
    (∀ p ∈ R, |S.Q p.1 p.2 - qStar| ≤ B * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
      |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2)) →
    0 ≤ Nphi → 0 ≤ Nm →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal Nphi →
    comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal Nm →
    ∀ p ∈ R, outerComponentsAt Cn Ce S H phiStar yStar mStar qStar e eta L Nphi Nm p.1 p.2 := by
  obtain ⟨Cn, hCn, hcomp⟩ := outer_source_components_of_bounds (Kstatic + 1) Cp (by linarith) hCp
  refine ⟨Cn, hCn, ?_⟩
  intro B hB
  obtain ⟨Ce, hCe, hcomp⟩ := hcomp B hB
  refine ⟨Ce, hCe, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm Bboundary Ct
  dsimp only
  intro h hLzero hstop hcontrols hNp hNm hw hm p hp
  have st := h.static_bounds (S.r p.1 p.2) hp.2
  have box := h.box p hp
  have hpsi : ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1 := by
    calc
      _ = ‖scalarComparison S H phiStar p.1 p.2 +
          (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by rw [scalarComparison, sub_add_cancel]
      _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ +
          ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := norm_add_le _ _
      _ ≤ Kstatic + 1 := by
        have hh := norm_le_of_comparisonNorm_le (by norm_num : (0 : ℝ) ≤ 1) hp
          (by simpa only [ENNReal.ofReal_one] using hstop)
        linarith only [hh, st.2.2.2.1]
  have hrp : 0 < S.r p.1 p.2 := zero_lt_one.trans_le (hLzero.trans hp.2.1)
  have ha : (-S.nu p.1 p.2) * S.lam p.1 p.2 ∈ Icc 0 1 := by
    constructor
    · exact mul_nonneg (by linarith only [box.1.2]) (by linarith only [box.2.1.1])
    · have hh := mul_le_mul (by linarith only [box.1.1] : -S.nu p.1 p.2 ≤ 1 / 2)
        box.2.1.2 (by linarith only [box.2.1.1] : 0 ≤ S.lam p.1 p.2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      linarith only [hh]
  exact hcomp (S.r p.1 p.2) L (S.m p.1 p.2) (mStar (S.r p.1 p.2))
    (S.Q p.1 p.2) qStar e eta (S.A p.1 p.2) ((-S.nu p.1 p.2) * S.lam p.1 p.2)
    (S.lam p.1 p.2) Nphi Nm H (shiftedRphi S H p.1 p.2)
    (scalarComparison S H phiStar p.1 p.2) (yStar (S.r p.1 p.2))
    (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2)) (hLzero.trans hp.2.1)
    ((zero_lt_one.trans_le hLzero).trans_le h.ordered) h.errors.2.1
    (by rw [abs_of_nonneg box.2.2.1.1]; exact box.2.2.1.2) box.2.2.2
    st.2.2.2.2.2 ha ⟨by linarith only [box.2.1.1], box.2.1.2.trans (by norm_num)⟩
    (hcontrols p hp).2.1 h.reference_charge (hcontrols p hp).1 h.scale (hcontrols p hp).2.2
    (norm_le_of_comparisonNorm_le hNp hp hw)
    (by simpa only [massComparison, Real.norm_eq_abs] using norm_le_of_comparisonNorm_le hNm hp hm)
    hpsi (st.2.1.trans (by gcongr; linarith)) (st.2.2.2.2.1.trans (by gcongr; linarith))

end EmcsfAcExtension.Global.Observation
