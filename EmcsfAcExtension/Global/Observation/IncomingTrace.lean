module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Global.Observation.IncomingTransfer
import EmcsfAcExtension.Global.Observation.OuterMass
import EmcsfAcExtension.Global.Observation.InnerMass
import EmcsfAcExtension.Global.Observation.OuterClosure
import EmcsfAcExtension.Global.Observation.InnerNormalization
public import EmcsfAcExtension.Global.Observation.InnerTransport
import EmcsfAcExtension.Infra.Gronwall

/-! # Reconstruction of the incoming scalar ratio

The ordinary derivative must be converted back to the covariant scalar
ratio with its electromagnetic correction. No incoming supremum bound is
introduced. Source: charged_SF_new_version.tex:L2561–L2583; internal project record (Z) and (Z1).
-/

public section

open Complex Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [internal]
Reconstruct the incoming ratio from the derivative of the literal
comparison variable. The positive connection correction is essential.
All differential premises are characteristic equations or the reference
radial equation, rather than a comparison estimate. -/
theorem Observation.incoming_scalar_reconstruction_of_equations
    (S : Fields) (e : ℝ) (H : ℂ) (phiStar : ℝ → ℂ) {u v : ℝ} (yStar : ℂ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hdr : HasDerivAt (fun x => S.r x v) (S.nu u v) u)
    (hdphi : HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u)
    (hdf : HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r)
      (phiStar (S.r u v) + yStar) (S.r u v)) :
    S.xi u v / S.nu u v - yStar =
      deriv (fun x => scalarComparison S H phiStar x v) u / S.nu u v -
        scalarComparison S H phiStar u v / S.r u v +
        I * e * S.A u v * S.r u v * S.phi u v / S.nu u v := by
  rw [(Observation.scalar_comparison_in_deriv_of_equations
    S e H phiStar yStar hr hn hdr hdphi hdf).deriv]
  have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  field_simp [hnC]; ring

/-- [internal]
The triangle estimate used after derivative transfer. The exact
coefficients depend only on the lower expansion bound `c` and radius
`r`; the same-label boundary value `g` remains visible and unsquared.
The outer consumer must discharge the reconstruction and transfer
premises. No smallness of `g` is required. -/
theorem Observation.incoming_pointwise_of_transfer
    {z w wU g correction : ℂ} {nu r c E W B : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hnu : c ≤ |nu|)
    (hrec : z = wU / (nu : ℂ) - w / (r : ℂ) + correction)
    (htransfer : ‖wU + g / 2‖ ≤ E) (hw : ‖w‖ ≤ W)
    (hcorrection : ‖correction‖ ≤ B) :
    ‖z‖ ≤ (‖g‖ / 2 + E) / c + W / r + B := by
  have hn : 0 < |nu| := hc.trans_le hnu
  have hwu : ‖wU‖ ≤ ‖g‖ / 2 + E := by
    calc
      ‖wU‖ = ‖(wU + g / 2) - g / 2‖ := by congr 1; ring
      _ ≤ ‖wU + g / 2‖ + ‖g / 2‖ := norm_sub_le _ _
      _ ≤ E + ‖g‖ / 2 := by simpa using add_le_add_right htransfer (‖g / 2‖)
      _ = ‖g‖ / 2 + E := add_comm _ _
  have hwu0 : 0 ≤ ‖g‖ / 2 + E := (norm_nonneg wU).trans hwu
  have hd : ‖wU / (nu : ℂ)‖ ≤ (‖g‖ / 2 + E) / c := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_right hwu hn.le).trans
      (div_le_div_of_nonneg_left hwu0 hc hnu)
  have hw' : ‖w / (r : ℂ)‖ ≤ W / r := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_le_div_of_nonneg_right hw hr.le
  rw [hrec]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hd hw')) hcorrection)

/-- [internal]
The pointwise incoming estimate on the actual outer fields. All displayed
coefficients depend only on the prior outer coefficients and shifted
scalar bound, uniformly in the radius, scale, background and coupling.
The boundary datum stays unsquared and at the same label. Both the
ordinary derivative transfer and the retained potential are used. -/
theorem co_incoming_pointwise_of_outer
    {S : Fields} {H : ℂ} {phiStar yStar : ℝ → ℂ}
    {e u v r L K Cp Cn Ce Nphi Nm eta : ℝ}
    (hrdef : S.r u v = r) (hr : 1 ≤ r) (hrL : r ≤ L)
    (hK : 0 ≤ K) (hCp : 0 ≤ Cp) (hCn : 0 ≤ Cn) (_hCe : 0 ≤ Ce)
    (hNp : 0 ≤ Nphi) (_hNm : 0 ≤ Nm) (heta : 0 ≤ eta)
    (hnu : 1 / 8 ≤ |S.nu u v|) (hw : ‖scalarComparison S H phiStar u v‖ ≤ Nphi)
    (hpsi : ‖shiftedRphi S H u v‖ ≤ K)
    (hpotential : |e * S.A u v| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r u v))
    (htransfer : ‖((S.nu u v : ℂ) * (S.phi u v - H -
      (phiStar (S.r u v) + yStar (S.r u v))) + S.xi u v -
        I * e * S.A u v * S.r u v * S.phi u v) +
      (S.phi u u - H + S.xi u u / S.nu u u) / 2‖ ≤
        Cn * (Nphi + Nm) / r ^ 2 + Ce * eta / r ^ 3 +
          Ce * eta / L * Real.log (L / r)) :
    ‖S.xi u v / S.nu u v - yStar (S.r u v)‖ ≤
      4 * ‖S.phi u u - H + S.xi u u / S.nu u u‖ +
        (8 * Cn + 1) * Nphi / r + 8 * Cn * Nm / r ^ 2 + 8 * Ce * eta / r ^ 3 +
          eta / L * (8 * Ce * Real.log (L / r) + 8 * (K + 1) * Cp) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hLp : 0 < L := hrp.trans_le hrL
  have hnp : 0 < |S.nu u v| := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hnu
  have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mp hnp)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrp.ne'
  let wU := (S.nu u v : ℂ) *
    (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.xi u v -
      I * e * S.A u v * S.r u v * S.phi u v
  have hrec : S.xi u v / S.nu u v - yStar (S.r u v) =
      wU / S.nu u v - scalarComparison S H phiStar u v / r +
        I * e * S.A u v * S.r u v * S.phi u v / S.nu u v := by
    dsimp only [wU, scalarComparison, shiftedRphi]
    rw [hrdef]
    field_simp [hnC, hrC]
    ring
  have hcorrection := Observation.incoming_connection_correction_of_outer hK
    (by rwa [hrdef]) hLp heta hCp hnu hpsi hpotential
  have hraw := Observation.incoming_pointwise_of_transfer
    (by norm_num : (0 : ℝ) < 1 / 8) hrp hnu hrec htransfer hw hcorrection
  have hrr : r ≤ r ^ 2 := by nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr)]
  have hneutral := div_le_div_of_nonneg_left (by positivity : 0 ≤ 8 * Cn * Nphi) hrp hrr
  calc
    _ ≤ 4 * ‖S.phi u u - H + S.xi u u / S.nu u u‖ +
        8 * Cn * Nphi / r ^ 2 + Nphi / r + 8 * Cn * Nm / r ^ 2 +
        8 * Ce * eta / r ^ 3 + eta / L *
          (8 * Ce * Real.log (L / r) + 8 * (K + 1) * Cp) := hraw.trans_eq (by ring)
    _ ≤ _ := by linear_combination hneutral

/-- [node prop:charged-observation#incoming-derivative-transfer]
[node prop:charged-observation#incoming-scalar-reconstruction]
[node eq:co-incoming-pointwise]
Incoming comparison on the entire actual outer region from raw
normalized data. Both outer comparison hypotheses of the transfer helper
are discharged by `outer_comparison_of_normalization`. Constants are
chosen after the fixed static bound, then boundary coefficients, before
all fields, radii, backgrounds and errors. The incoming boundary value
remains the same-label function, with no pointwise smallness premise. -/
theorem Observation.incoming_comparison_of_normalization
    (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin Cm Cp Cn : ℝ, 0 < Lmin ∧ 0 < Cm ∧ 0 < Cp ∧ 0 < Cn ∧
    ∀ Ct Bboundary : ℝ, 0 ≤ Ct → 0 ≤ Bboundary →
    ∃ CB CE Ce Cq : ℝ, 0 < CB ∧ 0 < CE ∧ 0 < Ce ∧ 0 < Cq ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    let Nphi := 4 * (CB * epsilon + CE * eta)
    let Nm := Cm * (CB * epsilon + CE * eta) / Lzero
    Observation.OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    Lmin ≤ Lzero → Nphi ≤ 1 / 2 → Cq * eta ≤ 1 →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal Nphi ∧
    comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal Nm ∧
    ∀ p ∈ R,
      ‖((S.nu p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H -
        (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2))) + S.xi p.1 p.2 -
          I * e * S.A p.1 p.2 * S.r p.1 p.2 * S.phi p.1 p.2) +
        (S.phi p.1 p.1 - H + S.xi p.1 p.1 / S.nu p.1 p.1) / 2‖ ≤
        Cn * (Nphi + Nm) / S.r p.1 p.2 ^ 2 + Ce * eta / S.r p.1 p.2 ^ 3 +
          Ce * eta / L * Real.log (L / S.r p.1 p.2) ∧
      ‖S.xi p.1 p.2 / S.nu p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
        4 * ‖S.phi p.1 p.1 - H + S.xi p.1 p.1 / S.nu p.1 p.1‖ +
        (8 * Cn + 1) * Nphi / S.r p.1 p.2 + 8 * Cn * Nm / S.r p.1 p.2 ^ 2 +
        8 * Ce * eta / S.r p.1 p.2 ^ 3 + eta / L *
          (8 * Ce * Real.log (L / S.r p.1 p.2) + 8 * (Kstatic + 2) * Cp) ∧
      S.xi p.1 p.2 / S.nu p.1 p.2 - yStar (S.r p.1 p.2) =
        deriv (fun u => scalarComparison S H phiStar u p.2) p.1 / S.nu p.1 p.2 -
          scalarComparison S H phiStar p.1 p.2 / S.r p.1 p.2 +
            I * e * S.A p.1 p.2 * S.r p.1 p.2 * S.phi p.1 p.2 / S.nu p.1 p.2 ∧
      ‖I * e * S.A p.1 p.2 * S.r p.1 p.2 * S.phi p.1 p.2 / S.nu p.1 p.2‖ ≤
        8 * (Kstatic + 2) * Cp * eta / L := by
  obtain ⟨Lmin, Cm, hLmin, hCm, houterConstants⟩ :=
    Observation.outer_comparison_of_normalization Kstatic hKs
  obtain ⟨Cp, Cn, hCp, hCn, hincomingConstants⟩ :=
    Observation.incoming_transfer_of_raw_outer_estimates Kstatic hKs
  refine ⟨max Lmin 1, Cm, Cp, Cn, lt_of_lt_of_le hLmin (le_max_left _ _), hCm, hCp, hCn, ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨CB, CE, CqO, hCB, hCE, hCqO, houter⟩ := houterConstants Ct Bboundary hCt hB
  obtain ⟨Ce, CqI, hCe, hCqI, hincoming⟩ := hincomingConstants Bboundary hB
  refine ⟨CB, CE, Ce, max CqO CqI, hCB, hCE, hCe,
    lt_of_lt_of_le hCqO (le_max_left _ _), ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e
  dsimp only
  intro h hLzero hsmall hcharged
  let R := sidewaysTruncation S D a b Lzero L
  let Nphi := 4 * (CB * epsilon + CE * eta)
  let Nm := Cm * (CB * epsilon + CE * eta) / Lzero
  have hL1 : 1 ≤ Lzero := (le_max_right _ _).trans hLzero
  have hLp : 0 < Lzero := zero_lt_one.trans_le hL1
  have he : 0 ≤ epsilon := h.errors.1.1
  have heta : 0 ≤ eta := h.errors.2.1
  have hNp : 0 ≤ Nphi := by dsimp [Nphi]; positivity
  have hNm : 0 ≤ Nm := by dsimp [Nm]; positivity
  have hstop : Nphi ≤ 1 := hsmall.trans (by norm_num)
  have hchargedO : CqO * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) heta).trans hcharged
  have hchargedI : CqI * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) heta).trans hcharged
  have ho := houter S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e
    ((le_max_left _ _).trans hLzero) h.ordered he h.errors.1.2 heta h.errors.2.2
    hsmall hchargedO h.reference_charge h.scale h.compact h.fields h.static_mass_ac
    h.static_continuous.1 h.static_continuous.2 h.static_boundary.1 h.static_boundary.2
    h.static_equations h.static_bounds h.base h.triangles h.box h.equations h.boundary
  have hi := hincoming Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
    h hL1 hCt hchargedI hNp hstop hNm ho.1 ho.2
  refine ⟨ho.1, ho.2, ?_⟩
  intro p hp
  have hr : 1 ≤ S.r p.1 p.2 := hL1.trans hp.2.1
  have hrp : 0 < S.r p.1 p.2 := zero_lt_one.trans_le hr
  have hn : S.nu p.1 p.2 < 0 := by linarith only [(h.box p hp).1.2]
  have hnu : 1 / 8 ≤ |S.nu p.1 p.2| := by
    rw [abs_of_neg hn]
    linarith only [(h.box p hp).1.2]
  have hw : ‖scalarComparison S H phiStar p.1 p.2‖ ≤ Nphi :=
    norm_le_of_comparisonNorm_le hNp hp ho.1
  have hpsi : ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1 := by
    calc
      _ = ‖scalarComparison S H phiStar p.1 p.2 +
          (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by
        simp only [scalarComparison, sub_add_cancel]
      _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ +
          ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [hw, hstop, (h.static_bounds (S.r p.1 p.2) hp.2).2.2.2.1]
  refine ⟨hi.2 p hp, ?_, ?_, ?_⟩
  · exact (co_incoming_pointwise_of_outer rfl hr hp.2.2 (by positivity)
      hCp.le hCn.le hCe.le hNp hNm heta hnu hw hpsi (hi.1 p hp) (hi.2 p hp)).trans_eq (by ring)
  · exact Observation.incoming_scalar_reconstruction_of_equations S e H phiStar
      (yStar (S.r p.1 p.2)) hrp.ne' hn.ne
      (h.equations p hp).1 (h.equations p hp).2.2.2.2.2.2.2.1
      (h.static_equations (S.r p.1 p.2) hp.2).1
  · exact (Observation.incoming_connection_correction_of_outer (by positivity) hr
      (hrp.trans_le hp.2.2) heta hCp.le hnu hpsi (hi.1 p hp)).trans_eq (by ring)

/-- [internal]
The non-boundary part of the incoming estimate is uniformly small on
the outer annulus. Its explicit coefficient depends only on the fixed
outer coefficients, uniformly in both radial endpoints and errors.
The finite logarithm is controlled without increasing the incoming
boundary datum to a pointwise bound. -/
theorem Observation.incoming_remainder_of_outer
    {r L Lzero CB CE Cm Cn Ce Cp K epsilon eta : ℝ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hLzero : 1 ≤ Lzero)
    (hCB : 0 ≤ CB) (hCE : 0 ≤ CE) (hCm : 0 ≤ Cm) (hCn : 0 ≤ Cn)
    (hCe : 0 ≤ Ce) (hCp : 0 ≤ Cp) (hK : 0 ≤ K)
    (he : 0 ≤ epsilon) (heta : 0 ≤ eta) :
    (8 * Cn + 1) * (4 * (CB * epsilon + CE * eta)) / r +
      8 * Cn * (Cm * (CB * epsilon + CE * eta) / Lzero) / r ^ 2 +
      8 * Ce * eta / r ^ 3 + eta / L * (8 * Ce * Real.log (L / r) + 8 * (K + 2) * Cp) ≤
      (((8 * Cn + 1) * 4 + 8 * Cn * Cm) * (CB + CE) + 16 * Ce + 8 * (K + 2) * Cp) *
        (epsilon + eta) := by
  have hL : 1 ≤ L := hr.trans hrL
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have herr : CB * epsilon + CE * eta ≤ (CB + CE) * (epsilon + eta) := by
    have hh := mul_nonneg hCB heta
    have hh' := mul_nonneg hCE he
    nlinarith only [hh, hh']
  have hb := (div_le_self
    (by positivity : 0 ≤ (8 * Cn + 1) * (4 * (CB * epsilon + CE * eta))) hr).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 4))
      (by positivity : 0 ≤ 8 * Cn + 1))
  have hm0 : 0 ≤ Cm * (CB * epsilon + CE * eta) := by positivity
  have hm := (div_le_self
    (by positivity : 0 ≤ 8 * Cn * (Cm * (CB * epsilon + CE * eta) / Lzero))
    (one_le_pow₀ hr (n := 2))).trans
      (mul_le_mul_of_nonneg_left ((div_le_self hm0 hLzero).trans
        (mul_le_mul_of_nonneg_left herr hCm)) (by positivity : 0 ≤ 8 * Cn))
  have hel := div_le_self (by positivity : 0 ≤ 8 * Ce * eta) (one_le_pow₀ hr (n := 3))
  have hlog : Real.log (L / r) / L ≤ 1 := (outer_log_div_bounds hrp hrL).1.trans
    (by simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hr)
  have hlog' := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 8 * Ce * eta)
  have hpot := mul_le_mul_of_nonneg_left (div_le_self heta hL)
    (by positivity : 0 ≤ 8 * (K + 2) * Cp)
  have hextra := mul_nonneg (show 0 ≤ 16 * Ce + 8 * (K + 2) * Cp by positivity) he
  have hlast : eta / L * (8 * Ce * Real.log (L / r) + 8 * (K + 2) * Cp) ≤
      8 * Ce * eta + (8 * (K + 2) * Cp) * eta := by
    have hh := add_le_add hlog' hpot
    convert hh using 1 <;> ring
  linarith only [hb, hm, hel, hlast, hextra]

/-- [node prop:charged-observation#incoming-L2-inner-trace]
The incoming error on the fixed inner cylinder is small in its actual
clock measure. Constants are fixed after `Kstatic,Ct,Bboundary,Kwindow`,
before all fields, outer radii, backgrounds, couplings and errors.
The only incoming boundary input is the full squared L² integral.
The clock substitution retains the same representative, and its
Jacobian is the actual density `2*(-nu)`, bounded by one. -/
theorem Observation.incoming_l2_inner_trace_of_normalization
    (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin > 0, ∀ Ct Bboundary : ℝ, 0 ≤ Ct → 0 ≤ Bboundary →
    ∃ CB CE Cq : ℝ, 0 < CB ∧ 0 < CE ∧ 0 < Cq ∧
    ∀ Kwindow : ℝ, 0 ≤ Kwindow → ∃ C > 0,
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e : ℝ)
      (Vzero : ℝ → ℝ) (tau : ℝ ≃o ℝ) (u₀ u₁ : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    let g := fun u => S.phi u u - H + S.xi u u / S.nu u u
    Observation.OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    Lmin ≤ Lzero → 4 * (CB * epsilon + CE * eta) ≤ 1 / 2 → Cq * eta ≤ 1 →
    a ≤ u₀ → u₀ ≤ u₁ → u₁ ≤ b → ContinuousOn Vzero (Icc u₀ u₁) →
    ContDiff ℝ 1 (tau : ℝ → ℝ) →
    (∀ u ∈ Icc u₀ u₁, (u, Vzero u) ∈ R ∧ S.r u (Vzero u) = Lzero ∧
      deriv (tau : ℝ → ℝ) u = 2 * (-S.nu u (Vzero u))) →
    tau u₁ - tau u₀ ≤ Kwindow → IntervalIntegrable (fun u => ‖g u‖ ^ 2) volume a b →
    (∫ u in a..b, ‖g u‖ ^ 2) ≤ epsilon ^ 2 / L →
    (∫ t in tau u₀..tau u₁,
      ‖S.xi (tau.symm t) (Vzero (tau.symm t)) /
          S.nu (tau.symm t) (Vzero (tau.symm t)) -
        yStar (S.r (tau.symm t) (Vzero (tau.symm t)))‖ ^ 2) ≤ (C * (epsilon + eta)) ^ 2 := by
  obtain ⟨Lmin, Cm, Cp, Cn, hLmin, hCm, hCp, hCn, hconstants⟩ :=
    Observation.incoming_comparison_of_normalization Kstatic hKs
  refine ⟨max Lmin 1, lt_of_lt_of_le hLmin (le_max_left _ _), ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨CB, CE, Ce, Cq, hCB, hCE, hCe, hCq, hincoming⟩ := hconstants Ct Bboundary hCt hB
  refine ⟨CB, CE, Cq, hCB, hCE, hCq, ?_⟩
  intro Kwindow hKwindow
  let B := (((8 * Cn + 1) * 4 + 8 * Cn * Cm) * (CB + CE) +
    16 * Ce + 8 * (Kstatic + 2) * Cp)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨C, hC, htrace⟩ := Observation.incoming_l2_trace_of_pointwise
    4 B Kwindow (by norm_num) hB0 hKwindow
  refine ⟨C, hC, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Vzero tau u₀ u₁
  dsimp only
  intro h hLzero hsmall hcharged hau huv hub cV htau hcurve hlength hgi hgb
  let R := sidewaysTruncation S D a b Lzero L
  let g := fun u => S.phi u u - H + S.xi u u / S.nu u u
  let z := fun u => S.xi u (Vzero u) / S.nu u (Vzero u) - yStar (S.r u (Vzero u))
  have hL1 : 1 ≤ Lzero := (le_max_right _ _).trans hLzero
  have hL : 1 ≤ L := hL1.trans h.ordered
  have hin := hincoming S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e
    h ((le_max_left _ _).trans hLzero) hsmall hcharged
  rcases h.fields with ⟨cr, cn, _cl, _ca, cp, _ct, _cm, _cq⟩
  have cpair : ContinuousOn (fun u => (u, Vzero u)) (Icc u₀ u₁) :=
    continuousOn_id.prodMk cV
  have hmem (u) (hu : u ∈ Icc u₀ u₁) := (hcurve u hu).1
  have hn (u) (hu : u ∈ Icc u₀ u₁) : S.nu u (Vzero u) ≠ 0 := by
    have hh := (h.box (u, Vzero u) (hmem u hu)).1.2
    linarith only [hh]
  have cz : ContinuousOn z (Icc u₀ u₁) :=
    ((h.incoming_continuous.comp cpair hmem).div
      (Complex.continuous_ofReal.comp_continuousOn (cn.comp cpair hmem))
      (fun u hu => Complex.ofReal_ne_zero.mpr (hn u hu))).sub
      (h.static_continuous.2.comp (cr.comp cpair hmem) (fun u hu => (hmem u hu).2))
  have hdiag (u) (hu : u ∈ Icc u₀ u₁) : (u, u) ∈ R :=
    h.triangles (u, Vzero u) (hmem u hu)
      (sidewaysTriangle_outgoing ⟨(hmem u hu).1.2.2.1, le_rfl⟩)
  have cdiag : ContinuousOn (fun u : ℝ => (u, u)) (Icc u₀ u₁) :=
    continuousOn_id.prodMk continuousOn_id
  have cg : ContinuousOn g (Icc u₀ u₁) :=
    ((cp.comp cdiag hdiag).sub continuousOn_const).add
      ((h.incoming_continuous.comp cdiag hdiag).div
        (Complex.continuous_ofReal.comp_continuousOn (cn.comp cdiag hdiag))
        (fun u hu => Complex.ofReal_ne_zero.mpr (by
          rw [h.incoming_boundary u (hdiag u hu)]
          norm_num)))
  have cclock : Continuous (deriv (tau : ℝ → ℝ)) := (contDiff_one_iff_deriv.mp htau).2
  have hclockIntegral : (∫ u in u₀..u₁, deriv (tau : ℝ → ℝ) u) = tau u₁ - tau u₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv htau.continuous.continuousOn
      (fun u _ => ((contDiff_one_iff_deriv.mp htau).1 u).hasDerivAt)
      (cclock.intervalIntegrable u₀ u₁)
  have hgbSub : (∫ u in u₀..u₁, ‖g u‖ ^ 2) ≤ epsilon ^ 2 := by
    have hi := intervalIntegral.integral_mono_interval hau huv hub
      (Filter.Eventually.of_forall (fun u => sq_nonneg ‖g u‖)) hgi
    exact (hi.trans hgb).trans (div_le_self (sq_nonneg epsilon) hL)
  change (∫ t in tau u₀..tau u₁, ‖z (tau.symm t)‖ ^ 2) ≤ _
  rw [Observation.incoming_trace_clock_integral tau htau
    (fun _ => tau.monotone.deriv_nonneg)]
  apply htrace z g (deriv (tau : ℝ → ℝ)) u₀ u₁ epsilon eta huv cz cg cclock.continuousOn
    h.errors.1.1 h.errors.2.1
  · intro u hu
    refine ⟨tau.monotone.deriv_nonneg, ?_⟩
    rw [(hcurve u hu).2.2]
    linarith only [(h.box (u, Vzero u) (hmem u hu)).1.1]
  · exact hclockIntegral.trans_le hlength
  · exact hgbSub
  · intro u hu
    have hp := (hin.2.2 (u, Vzero u) (hmem u hu)).2.1
    have hr : 1 ≤ S.r u (Vzero u) := by rw [(hcurve u hu).2.1]; exact hL1
    have hrem := Observation.incoming_remainder_of_outer hr (hmem u hu).2.2 hL1
      hCB.le hCE.le hCm.le hCn.le hCe.le hCp.le hKs h.errors.1.1 h.errors.2.1
    dsimp only [z, g, B]
    linarith only [hp, hrem]

/-- [internal]
All inner transport and electric mass sources from the primitive annular
controls. Constants depend only on the displayed fixed bounds, before
the reference member, fields, background, coupling, errors and window.
The geometric and charged envelopes are discharged by their proved
annular lemmas; no comparison or transport estimate is assumed. -/
theorem Observation.inner_sources_of_normalization
    (rStar delta c K Qmax Cscalar Bcharge Amax : ℝ)
    (hrStar : 0 < rStar) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) :
    ∃ A B E : ℝ, 0 < A ∧ 0 < B ∧ 0 < E ∧
    ∀ (rho Lzero G : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e eta etheta em exi : ℝ),
    rStar ≤ rho → Observation.InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta etheta em exi →
    ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      let r := S.r p.1 p.2
      let Y := S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ) - yStar r
      let Z := S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ) - yStar r
      let k := (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / r ^ 2) / (1 - S.mu p.1 p.2)
      let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
      let electric := I * e * S.Q p.1 p.2 * S.phi p.1 p.2 / ((1 - S.mu p.1 p.2) * r : ℝ)
      let potential := I * e * S.A p.1 p.2 * yStar r
      |k / r| ≤ A ∧
      ‖-((1 / r : ℝ) : ℂ) * Y - (((k - ks) / r : ℝ) : ℂ) * yStar r + electric‖ ≤
        B * (‖Y‖ + |massComparison S mStar p.1 p.2| + eta) ∧
      ‖((-S.nu p.1 p.2 : ℝ) : ℂ) *
        (((1 / r : ℝ) : ℂ) * Z + ((k / r : ℝ) : ℂ) * Y +
          (((k - ks) / r : ℝ) : ℂ) * yStar r + electric) - potential‖ ≤
        (-S.nu p.1 p.2) * B * (‖Z‖ + ‖Y‖ + |massComparison S mStar p.1 p.2| + eta) ∧
      |(S.Q p.1 p.2 ^ 2 - qStar ^ 2) / (2 * r ^ 2)| ≤ E * eta := by
  obtain ⟨Cg, hCg, hgeo⟩ := Observation.inner_geometric_source_bound
    rStar delta Qmax Bcharge hrStar hdelta hQmax hBq
  obtain ⟨Ce, hCe, hcharged⟩ := Observation.inner_charged_source_bound
    rStar delta Qmax Cscalar K Amax hrStar hdelta hQmax hCs hK hAm
  let A := (4 / rStar + Qmax ^ 2 / rStar ^ 2) / (delta * rStar)
  let Ad := Cg * K / rStar
  let B := 1 / rStar + A + Ad + Ce + Ce / c
  let E := Qmax * Bcharge / rStar ^ 2 + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hAd : 0 ≤ Ad := by dsimp [Ad]; positivity
  refine ⟨A, B, E, hA, by dsimp [B]; positivity, by dsimp [E]; positivity, ?_⟩
  intro rho Lzero G S D H yStar mStar a b qStar e eta etheta em exi hrho h p hp
  dsimp only
  let r := S.r p.1 p.2
  let k := (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / r ^ 2) / (1 - S.mu p.1 p.2)
  let ks := (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  have hr : rStar ≤ r := hrho.trans hp.2.1
  have hrp : 0 < r := hrStar.trans_le hr
  have hg : 0 < 1 - S.mu p.1 p.2 := hdelta.trans_le (h.box p hp).2.2.2
  have heta : 0 ≤ eta := h.errors.1
  have hst := h.static_bounds r hp.2
  have hq := h.charged p hp
  have hmu : |2 * S.m p.1 p.2 / r| ≤ 4 / rStar := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (h.box p hp).2.2.1.1, abs_of_pos hrp]
    exact (div_le_div_of_nonneg_right (by linarith only [(h.box p hp).2.2.1.2]) hrp.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hrStar hr)
  have hq2 : S.Q p.1 p.2 ^ 2 ≤ Qmax ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hQmax).mpr hq.2.1
  have hqfrac : |S.Q p.1 p.2 ^ 2 / r ^ 2| ≤ Qmax ^ 2 / rStar ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ S.Q p.1 p.2 ^ 2 / r ^ 2)]
    exact (div_le_div_of_nonneg_right hq2 (sq_nonneg r)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hrStar)
        (pow_le_pow_left₀ hrStar.le hr 2))
  have hk : |k / r| ≤ A := by
    dsimp only [k, Fields.mu]
    dsimp only [Fields.mu] at hg
    rw [div_div, abs_div, abs_of_pos (mul_pos hg hrp)]
    exact (div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add hmu hqfrac))
      (mul_pos hg hrp).le).trans (div_le_div_of_nonneg_left (by positivity)
      (mul_pos hdelta hrStar) (mul_le_mul (h.box p hp).2.2.2 hr hrStar.le hg.le))
  have hdif : |k - ks| ≤ Cg * (|massComparison S mStar p.1 p.2| + eta) := by
    simpa only [k, ks, r, Fields.mu, massComparison] using
      hgeo r (S.m p.1 p.2) (mStar r) (S.Q p.1 p.2) qStar eta hr heta
        (h.box p hp).2.2.2 hst.2.1 hq.2.1 h.reference_charge hq.2.2.1
  have hb : ‖(((k - ks) / r : ℝ) : ℂ) * yStar r‖ ≤
      Ad * (|massComparison S mStar p.1 p.2| + eta) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hrp]
    have ht := mul_le_mul hdif hst.1 (norm_nonneg _) (by positivity : 0 ≤ Cg *
      (|massComparison S mStar p.1 p.2| + eta))
    have ht' := (div_le_div_of_nonneg_right ht hrp.le).trans
      (div_le_div_of_nonneg_left (by positivity) hrStar hr)
    convert ht' using 1 <;>
      simp only [Ad, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hcSources := hcharged r 1 (1 - S.mu p.1 p.2) (S.Q p.1 p.2) e eta (S.A p.1 p.2)
    H (S.phi p.1 p.2) (yStar r) hr le_rfl (h.box p hp).2.2.2 heta hq.2.1 hq.1 hst.1
    (by simpa only [mul_one] using h.scale) hq.2.2.2
  have he : ‖I * e * S.Q p.1 p.2 * S.phi p.1 p.2 /
      ((1 - S.mu p.1 p.2) * r : ℝ)‖ ≤ Ce * eta := by
    linarith only [hcSources, norm_nonneg (I * e * S.A p.1 p.2 * yStar r)]
  have hpot : ‖I * e * S.A p.1 p.2 * yStar r‖ ≤ Ce * eta := by
    linarith only [hcSources, norm_nonneg (I * e * S.Q p.1 p.2 * S.phi p.1 p.2 /
      ((1 - S.mu p.1 p.2) * r : ℝ))]
  have hlin := Observation.inner_linear_source_norms
    (Y := S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ) - yStar r)
    (Z := S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ) - yStar r)
    (by positivity : 0 ≤ 1 / rStar)
    hA.le hAd hCe.le hCe.le hc (h.box p hp).1.1 (abs_nonneg _) heta
    (show |1 / r| ≤ 1 / rStar by
      rw [abs_of_pos (one_div_pos.mpr hrp)]
      exact one_div_le_one_div_of_le hrStar hr) hk hb he hpot
  refine ⟨hk, hlin.1, hlin.2, ?_⟩
  have hs : |S.Q p.1 p.2 + qStar| ≤ 2 * Qmax :=
    (abs_add_le _ _).trans (by linarith only [hq.2.1, h.reference_charge])
  have hsq : |S.Q p.1 p.2 ^ 2 - qStar ^ 2| ≤ 2 * Qmax * Bcharge * eta := by
    rw [show S.Q p.1 p.2 ^ 2 - qStar ^ 2 =
      (S.Q p.1 p.2 - qStar) * (S.Q p.1 p.2 + qStar) by ring, abs_mul]
    exact (mul_le_mul hq.2.2.1 hs (abs_nonneg _) (mul_nonneg hBq heta)).trans_eq (by ring)
  rw [abs_div, abs_of_pos (mul_pos (by norm_num) (sq_pos_of_pos hrp))]
  have hi := (div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 2 * r ^ 2)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 2 * rStar ^ 2)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrStar.le hr 2) (by norm_num : (0 : ℝ) ≤ 2)))
  have hi' : _ ≤ (Qmax * Bcharge / rStar ^ 2) * eta := hi.trans_eq (by ring)
  exact hi'.trans (by dsimp only [E]; nlinarith only [heta])

/-- [internal]
Remove the temporary scalar stop from the coupled Volterra estimate.
The constants depend only on the fixed forcing coefficient `A`, kernel
coefficient `B` and maximum annular depth `Dmax`, uniformly in `F`, `N`,
the selected member's depth, and both errors. The upstream consumer
must derive the displayed Volterra inequality and boundary estimate;
they are not new premises of the observation proposition. -/
theorem Observation.inner_comparison_closure_of_volterra
    (A B Dmax : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hDmax : 0 ≤ Dmax) :
    ∃ C > 0, ∃ sigma > 0,
      ∀ (epsilon eta D : ℝ) (F N : ℝ → ℝ),
        0 ≤ epsilon → 0 ≤ eta → 0 ≤ D → D ≤ Dmax →
        epsilon + eta ≤ sigma →
        ContinuousOn F (Icc 0 D) → ContinuousOn N (Icc 0 D) →
        (∀ d ∈ Icc 0 D, 0 ≤ F d) → (∀ d ∈ Icc 0 D, 0 ≤ N d) →
        F 0 ≤ A * (epsilon + eta) →
        (∀ d ∈ Icc 0 D, (∀ s ∈ Icc 0 d, F s ≤ 1) →
          F d + N d ≤ A * (epsilon + eta) +
            B * ∫ s in 0..d, F s + N s) →
        ∀ d ∈ Icc 0 D, F d + N d ≤ C * (epsilon + eta) ∧ F d < 1 := by
  let C := (A + 1) * Real.exp (B * Dmax)
  have hC : 0 < C := mul_pos (by linarith only [hA]) (Real.exp_pos _)
  have hAC : A ≤ C := by
    have he : 1 ≤ Real.exp (B * Dmax) := Real.one_le_exp (mul_nonneg hB hDmax)
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ A + 1 by positivity)
    dsimp only [C]
    linarith only [hm]
  refine ⟨C, hC, 1 / (2 * C), by positivity, ?_⟩
  intro epsilon eta D F N hepsilon heta hD hDD hsmall hF hN _hF0 hN0 hinit hvolterra
  have herr : 0 ≤ epsilon + eta := add_nonneg hepsilon heta
  have hhalf : C * (epsilon + eta) ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp hsmall
    nlinarith only [hh]
  have hinit' : F 0 < 1 := by
    have hh := (mul_le_mul_of_nonneg_right hAC herr)
    linarith only [hinit, hh, hhalf]
  have hbound (d : ℝ) (hd : d ∈ Icc 0 D)
      (hstop : ∀ s ∈ Icc 0 d, F s ≤ 1) :
      ∀ t ∈ Icc 0 d, F t + N t ≤ C * (epsilon + eta) := by
    have hsub : Icc 0 d ⊆ Icc 0 D := Icc_subset_Icc le_rfl hd.2
    have hg := EmcsfAcExtension.le_exp_integral_of_le_integral hd.1
      ((hF.add hN).mono hsub)
      (intervalIntegrable_const (a := 0) (b := d) (c := B))
      (Filter.Eventually.of_forall (fun _ => hB))
      (C := A * (epsilon + eta)) (fun t ht => by
        simpa only [intervalIntegral.integral_const_mul, Pi.add_apply] using
          hvolterra t (hsub ht) (fun s hs => hstop s ⟨hs.1, hs.2.trans ht.2⟩))
    intro t ht
    have hexp : Real.exp (B * t) ≤ Real.exp (B * Dmax) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ht.2.trans (hd.2.trans hDD)) hB)
    have hmul := mul_le_mul_of_nonneg_left hexp (mul_nonneg hA herr)
    have hrest := mul_le_mul_of_nonneg_right
      (show A ≤ A + 1 by linarith) (mul_nonneg herr (Real.exp_pos (B * Dmax)).le)
    calc
      F t + N t ≤ A * (epsilon + eta) * Real.exp (B * t) := by
        simpa only [Pi.add_apply, intervalIntegral.integral_const, smul_eq_mul,
          sub_zero, mul_comm t B] using hg t ht
      _ ≤ A * (epsilon + eta) * Real.exp (B * Dmax) := hmul
      _ ≤ C * (epsilon + eta) := by
        simpa only [C, mul_comm, mul_left_comm, mul_assoc] using hrest
  have hstopall : ∀ d ∈ Icc 0 D, F d < 1 := by
    by_contra hfail
    push Not at hfail
    obtain ⟨d, hd, hbad⟩ := hfail
    have hcross : ∃ t ∈ Icc 0 d, F t = 1 :=
      intermediate_value_Icc hd.1 (hF.mono (Icc_subset_Icc le_rfl hd.2))
        ⟨hinit'.le, hbad⟩
    let E := Icc 0 D ∩ F ⁻¹' ({1} : Set ℝ)
    have hEc : IsCompact E := isCompact_Icc.of_isClosed_subset
      (hF.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    have hEn : E.Nonempty := by
      obtain ⟨t, ht, htF⟩ := hcross
      exact ⟨t, ⟨⟨ht.1, ht.2.trans hd.2⟩, htF⟩⟩
    obtain ⟨d₀, hd₀, hmin⟩ := hEc.exists_isMinOn hEn continuousOn_id
    have heq : F d₀ = 1 := hd₀.2
    have hstop : ∀ s ∈ Icc 0 d₀, F s ≤ 1 := by
      intro s hs
      by_contra hnot
      have hsbad : 1 < F s := lt_of_not_ge hnot
      obtain ⟨t, ht, htF⟩ := intermediate_value_Icc hs.1
        (hF.mono (Icc_subset_Icc le_rfl (hs.2.trans hd₀.1.2))) ⟨hinit'.le, hsbad.le⟩
      have htE : t ∈ E := ⟨⟨ht.1, ht.2.trans (hs.2.trans hd₀.1.2)⟩, htF⟩
      have hdt : d₀ ≤ t := hmin htE
      have hsd : s = d₀ := le_antisymm hs.2 (hdt.trans ht.2)
      have hFs : F s = 1 := by simpa only [hsd] using heq
      exact (ne_of_gt hsbad) hFs
    have hbd := hbound d₀ hd₀.1 hstop d₀ ⟨hd₀.1.1, le_rfl⟩
    have hn := hN0 d₀ hd₀.1
    linarith only [hbd, hn, heq, hhalf]
  intro d hd
  exact ⟨hbound D ⟨hD, le_rfl⟩ (fun s hs => (hstopall s hs).le) d hd,
    hstopall d hd⟩

end EmcsfAcExtension.Global
