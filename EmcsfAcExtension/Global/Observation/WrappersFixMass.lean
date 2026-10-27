module

public import EmcsfAcExtension.Global.Observation.WrappersMass
import EmcsfAcExtension.Global.Observation.OuterMass
import Mathlib

/-! # Separate boundary and electric coefficients for the outer mass estimate

internal project record: retain the boundary witness before the electric coefficients.
Source: charged_SF_new_version.tex:L2497–2531; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal] The radial mass polynomial with its boundary coefficient chosen
from `K,Ct` alone. The neutral coefficient depends only on `K,Cn`; electric
coefficients follow `Ce,B`. All choices precede radii, errors and profiles. -/
theorem co_outer_mass_with_separate_boundary (K Cn : ℝ) (hK : 0 ≤ K) (hCn : 0 ≤ Cn) :
    ∃ Cneutral : ℝ, 0 < Cneutral ∧ ∀ Ct : ℝ, 0 ≤ Ct →
      ∃ Cboundary : ℝ, 0 < Cboundary ∧ ∀ Ce B : ℝ,
      0 ≤ Ce → 0 ≤ B → ∃ Celectric : ℝ, 0 < Celectric ∧
      ∀ (L0 r L epsilon eta Nphi Nm qStar : ℝ)
        (D gStar Q : ℝ → ℝ) (y yStar : ℝ → ℂ),
      1 ≤ L0 → L0 ≤ r → r ≤ L → 0 ≤ epsilon → epsilon ≤ 1 →
      0 ≤ eta → eta ≤ 1 → 0 ≤ Nphi → 0 ≤ Nm → |qStar| ≤ 1 →
      AbsolutelyContinuousOnInterval D r L →
      ContinuousOn y (Icc r L) → ContinuousOn yStar (Icc r L) →
      ContinuousOn gStar (Icc r L) → ContinuousOn Q (Icc r L) →
      (∫ s in r..L, ‖y s‖^2) ≤ 8 → |D L| ≤ Ct*epsilon/L →
      (∀ s ∈ Icc r L, ‖yStar s‖ ≤ K/s ∧ |gStar s| ≤ 2 ∧
        |Q s| ≤ 2 ∧ |Q s-qStar| ≤ B*eta) →
      (∀ s ∈ Icc r L, ‖y s-yStar s‖ ≤ Ct*epsilon/L+Cn*Nphi/s+Cn*Nm/s^2+
        Ce*eta/s^3+Ce*eta/L*Real.log (L/s)) →
      (∀ᵐ s ∂volume.restrict (Icc r L), deriv D s = -(‖y s‖^2/s)*D s+
        ((Q s^2-qStar^2)/(2*s^2)+gStar s*(starRingEnd ℂ (yStar s)*(y s-yStar s)).re+
          gStar s/2*‖y s-yStar s‖^2)) →
      |D r| ≤ (Cboundary*epsilon+Celectric*eta)/L0+
        (Cneutral/L0)*(Nphi+Nphi^2)+(Cneutral/L0^2)*Nm+(Cneutral/L0^3)*Nm^2 := by
  obtain ⟨Cq, hCq, hcharge⟩ := co_electric_mass_error
  let E := Real.exp 8
  let A := 2*K*Cn+5*Cn^2+1
  refine ⟨E*A, by dsimp [E,A]; positivity, ?_⟩
  intro Ct hCt
  let Tb := Ct+2*K*Ct+5*Ct^2+1
  refine ⟨E*Tb, by dsimp [E,Tb]; positivity, ?_⟩
  intro Ce B hCe hB
  let Te := 6*K*Ce+15*Ce^2+Cq*B+1
  refine ⟨E*Te, by dsimp [E,Te]; positivity, ?_⟩
  intro L0 r L epsilon eta Nphi Nm qStar D gStar Q y yStar hL0 hL0r hrL
    heps heps1 heta heta1 hphi hm hq hD hy hys hg hQ henergy hboundary hstatic hscalar heq
  have hr : 1 ≤ r := hL0.trans hL0r
  have hrp : 0 < r := by linarith
  have hL : 0 < L := hrp.trans_le hrL
  have hs (s : ℝ) (h : s ∈ Icc r L) : 0 < s := hrp.trans_le h.1
  let Y := fun s => y s-yStar s
  let F := fun s => (Q s^2-qStar^2)/(2*s^2)+
    gStar s*(starRingEnd ℂ (yStar s)*Y s).re+gStar s/2*‖Y s‖^2
  have hY : ContinuousOn Y (Icc r L) := hy.sub hys
  have hchargeC : ContinuousOn (fun s => |Q s^2-qStar^2|/s^2) (Icc r L) :=
    ((hQ.pow 2).sub continuousOn_const).abs.div (continuousOn_id.pow 2)
      (fun s h => pow_ne_zero 2 (hs s h).ne')
  have hFc : ContinuousOn F (Icc r L) :=
    (((hQ.pow 2).sub continuousOn_const).div (continuousOn_const.mul (continuousOn_id.pow 2))
      (fun s h => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hs s h).ne'))).add
      (hg.mul (Complex.continuous_re.comp_continuousOn (hys.star.mul hY))) |>.add
      ((hg.div_const 2).mul (hY.norm.pow 2))
  have hFi : IntervalIntegrable F volume r L := hFc.intervalIntegrable_of_Icc hrL
  have ha : IntervalIntegrable (fun s => ‖y s‖^2/s) volume r L :=
    ((hy.norm.pow 2).div continuousOn_id (fun s h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hfactor (s : ℝ) (h : s ∈ Icc r L) :
      Real.exp (∫ t in r..s, ‖y t‖^2/t) ≤ E := by
    apply (Observation.backward_mass_integrating_factor_of_normalization
      hrp hrL hy henergy s h).trans
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hrp).mpr (by nlinarith only [hr]))
  have hmass := backward_mass_abs_le hrL hD ha hFi heq hfactor
  have hforce (s : ℝ) (h : s ∈ Icc r L) :
      |F s| ≤ |Q s^2-qStar^2|/s^2+2*K*(‖Y s‖/s)+‖Y s‖^2 := by
    obtain ⟨hysb,hgb,_,_⟩ := hstatic s h
    have hsp := hs s h
    have hre := Complex.abs_re_le_norm (starRingEnd ℂ (yStar s)*Y s)
    rw [norm_mul, Complex.norm_conj] at hre
    have hlin : |gStar s*(starRingEnd ℂ (yStar s)*Y s).re| ≤ 2*K*(‖Y s‖/s) := by
      rw [abs_mul]
      calc
        _ ≤ 2*(‖yStar s‖*‖Y s‖) := mul_le_mul hgb hre (abs_nonneg _) (by norm_num)
        _ ≤ 2*((K/s)*‖Y s‖) := by gcongr
        _ = _ := by ring
    have hquad : |gStar s/2*‖Y s‖^2| ≤ ‖Y s‖^2 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (sq_nonneg ‖Y s‖)]
      exact (mul_le_mul_of_nonneg_right ((div_le_one (by norm_num)).mpr hgb)
        (sq_nonneg _)).trans_eq (one_mul _)
    have hqc : |(Q s^2-qStar^2)/(2*s^2)| ≤ |Q s^2-qStar^2|/s^2 := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (sq_nonneg s)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (le_mul_of_one_le_left
          (sq_nonneg s) (by norm_num))
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hqc hlin)) hquad)
  have hiY : IntervalIntegrable (fun s => ‖Y s‖/s) volume r L :=
    (hY.norm.div continuousOn_id (fun s h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hiY2 : IntervalIntegrable (fun s => ‖Y s‖^2) volume r L :=
    (hY.norm.pow 2).intervalIntegrable_of_Icc hrL
  have hforcing : (∫ s in r..L, |F s|) ≤ Cq*B*eta/r+
      2*K*((Ct*epsilon+Cn*Nphi+3*(Ce*eta))/r+(Cn*Nm)/r^2)+
      (5*((Ct*epsilon)^2+(Cn*Nphi)^2+3*(Ce*eta)^2)/r+5*(Cn*Nm)^2/r^3) := by
    have hker := outer_scalar_mass_kernels hr hrL (by positivity : 0 ≤ Ct*epsilon)
      (by positivity : 0 ≤ Cn*Nphi) (by positivity : 0 ≤ Cn*Nm)
      (by positivity : 0 ≤ Ce*eta) hY hscalar
    have hiC : IntervalIntegrable (fun s => |Q s^2-qStar^2|/s^2) volume r L :=
      hchargeC.intervalIntegrable_of_Icc hrL
    calc
      _ ≤ ∫ s in r..L, |Q s^2-qStar^2|/s^2+2*K*(‖Y s‖/s)+‖Y s‖^2 :=
        intervalIntegral.integral_mono_on hrL hFi.abs
          ((hiC.add (hiY.const_mul (2*K))).add hiY2) hforce
      _ = (∫ s in r..L, |Q s^2-qStar^2|/s^2)+2*K*(∫ s in r..L, ‖Y s‖/s)+
          (∫ s in r..L, ‖Y s‖^2) := by
        rw [intervalIntegral.integral_add (hiC.add (hiY.const_mul (2*K))) hiY2,
          intervalIntegral.integral_add hiC (hiY.const_mul (2*K)),
          intervalIntegral.integral_const_mul]
      _ ≤ _ := add_le_add (add_le_add (hcharge r L B eta qStar Q hrp hrL hB heta hq hQ
          (fun s h => ⟨(hstatic s h).2.2.1, (hstatic s h).2.2.2⟩))
          (mul_le_mul_of_nonneg_left hker.1 (by positivity))) hker.2
  have hb2 : (Ct*epsilon)^2 ≤ Ct^2*epsilon := by
    calc
      (Ct*epsilon)^2 = Ct^2 * (epsilon*epsilon) := by ring
      _ ≤ Ct^2 * epsilon :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right heps heps1) (sq_nonneg Ct)
  have he2 : (Ce*eta)^2 ≤ Ce^2*eta := by
    calc
      (Ce*eta)^2 = Ce^2 * (eta*eta) := by ring
      _ ≤ Ce^2 * eta :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right heta heta1) (sq_nonneg Ce)
  have hpoly : |D L|+(∫ s in r..L, |F s|) ≤
      (Tb*epsilon+Te*eta)/r+(A/r)*(Nphi+Nphi^2)+(A/r^2)*Nm+(A/r^3)*Nm^2 := by
    calc
      _ ≤ Ct*epsilon/r+Cq*B*eta/r+
          2*K*((Ct*epsilon+Cn*Nphi+3*(Ce*eta))/r+(Cn*Nm)/r^2)+
          (5*(Ct^2*epsilon+(Cn*Nphi)^2+3*(Ce^2*eta))/r+5*(Cn*Nm)^2/r^3) := by
        have hbd := hboundary.trans (div_le_div_of_nonneg_left (by positivity) hrp hrL)
        have hsq : 5*((Ct*epsilon)^2+(Cn*Nphi)^2+3*(Ce*eta)^2)/r ≤
            5*(Ct^2*epsilon+(Cn*Nphi)^2+3*(Ce^2*eta))/r := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb2 le_rfl)
            (mul_le_mul_of_nonneg_left he2 (by norm_num))) (by norm_num : (0:ℝ) ≤ 5)) hrp.le
        linarith only [hbd, hforcing, hsq]
      _ ≤ _ := by
        apply le_of_sub_nonneg
        dsimp [A,Tb,Te]
        ring_nf
        positivity
  have hpoint : |D r| ≤ (E*Tb*epsilon+E*Te*eta)/r+
      (E*A/r)*(Nphi+Nphi^2)+(E*A/r^2)*Nm+(E*A/r^3)*Nm^2 := by
    apply hmass.trans
    convert mul_le_mul_of_nonneg_left hpoly (Real.exp_pos 8).le using 1
    dsimp [E]
    ring
  apply hpoint.trans
  gcongr

namespace Observation

/-- [internal] The regional mass polynomial with its boundary coefficient
chosen from `Kstatic,Ct` alone, before `Ce,B`. The neutral coefficient depends
only on `Kstatic,Cn`; every coefficient precedes all normalized fields. -/
theorem outer_mass_with_separate_boundary_of_normalization
    (Kstatic Cn : ℝ) (hKs : 0 ≤ Kstatic) (hCn : 0 ≤ Cn) :
    ∃ CnM : ℝ, 0 < CnM ∧ ∀ Ct : ℝ, 0 ≤ Ct →
    ∃ CbM : ℝ, 0 < CbM ∧ ∀ Ce B : ℝ,
    0 ≤ Ce → 0 ≤ B → ∃ CeM : ℝ, 0 < CeM ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b L₀ L epsilon eta qStar e Nphi Nm Bboundary : ℝ),
    let R := sidewaysTruncation S D a b L₀ L
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b L₀ L epsilon eta qStar e →
    1 ≤ L₀ → 0 ≤ Nphi → 0 ≤ Nm →
    (∀ p ∈ R, |S.Q p.1 p.2| ≤ 2 ∧ |S.Q p.1 p.2 - qStar| ≤ B * eta) →
    (∀ p ∈ R, ‖S.theta p.1 p.2 / S.lam p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
      4 * epsilon / L + (64 * Cn + 1) * Nphi / S.r p.1 p.2 +
        64 * Cn * Nm / S.r p.1 p.2 ^ 2 + 64 * Ce * eta / S.r p.1 p.2 ^ 3 +
          64 * Ce * eta / L * Real.log (L / S.r p.1 p.2)) →
    comparisonNorm R (massComparison S mStar) ≤
      ENNReal.ofReal ((CbM * epsilon + CeM * eta) / L₀ +
        (CnM / L₀) * (Nphi + Nphi ^ 2) + (CnM / L₀ ^ 2) * Nm + (CnM / L₀ ^ 3) * Nm ^ 2) := by
  obtain ⟨CnM, hCnM, hmass⟩ :=
    co_outer_mass_with_separate_boundary Kstatic (64 * Cn + 1) hKs (by positivity)
  refine ⟨CnM, hCnM, ?_⟩
  intro Ct hCt
  obtain ⟨CbM, hCbM, hmass⟩ := hmass (Ct + 4) (by positivity)
  refine ⟨CbM, hCbM, ?_⟩
  intro Ce B hCe hB
  obtain ⟨CeM, hCeM, hmass⟩ := hmass (64 * Ce) B (by positivity) hB
  refine ⟨CeM, hCeM, ?_⟩
  intro S D H P phiStar yStar mStar a b L₀ L epsilon eta qStar e Nphi Nm Bboundary
  dsimp only
  intro h hL₀ hNp hNm hcharge hscalarY
  let R := sidewaysTruncation S D a b L₀ L
  have hL₀p : 0 < L₀ := zero_lt_one.trans_le hL₀
  have hLL := h.ordered
  have hLp := hL₀p.trans_le hLL
  have he := h.errors.1.1
  have he1 := h.errors.1.2
  have heta := h.errors.2.1
  have heta1 := h.errors.2.2
  have hq := h.reference_charge
  rcases h.fields with ⟨hr, _hn, hl, _ha, _hp, htheta, hm, hQ⟩
  have hmsc : ContinuousOn mStar (Icc L₀ L) := by
    simpa only [uIcc_of_le hLL] using h.static_mass_ac.continuousOn
  have hms := h.static_mass_ac
  have hys := h.static_continuous.2
  have hstatic := h.static_bounds
  have hmsd (s) (hs : s ∈ Ioo L₀ L) := (h.static_equations s (Ioo_subset_Icc_self hs)).2.2
  have hboundary := h.boundary
  have hbox := h.box
  have hrout (p) (hp : p ∈ R) := (h.equations p hp).2.1
  have hmout (p) (hp : p ∈ R) := (h.equations p hp).2.2.1
  have hopt (p) (hp : p ∈ R) := continuousOn_outgoing_of_subtriangle hl (h.triangles p hp)
  apply comparisonNorm_le_of_bound (by positivity)
  intro p hp
  have hpR := hp
  have hpath := (sidewaysTruncation_paths (h.triangles p hp)).2
  have hpathR (t) (ht : t ∈ Icc p.2 p.1) : (p.1, t) ∈ R := hpath t ht
  have hcont {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) : ContinuousOn (f p.1) (Icc p.2 p.1) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn hpathR
  obtain ⟨inv, hrL, hci, hmem, hrad, hleft, hright, hdi, hy, hmr, hQr, hmd, hmac,
    hradbox, henergy⟩ :=
    outgoing_radial_mass_data_of_normalization S hp.1.2.2.1
      (hL₀p.trans_le hp.2.1) (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
      (hcont hr) (hopt p hpR) (hcont htheta) (hcont hm) (hcont hQ)
      (fun t ht => hrout (p.1, t) (hpathR t (Ioo_subset_Icc_self ht)))
      (fun t ht => hmout (p.1, t) (hpathR t (Ioo_subset_Icc_self ht)))
      (fun t ht => ⟨by linarith only [(hbox (p.1, t) (hpathR t ht)).2.1.1],
        (hbox (p.1, t) (hpathR t ht)).2.2⟩)
  let y := fun s => S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)
  let mr := fun s => S.m p.1 (inv s)
  let Qr := fun s => S.Q p.1 (inv s)
  let dm := fun s => mr s - mStar s
  let gs := fun s => 1 - 2 * mStar s / s
  have hinterval : Icc (S.r p.1 p.2) L ⊆ Icc L₀ L := Icc_subset_Icc hp.2.1 le_rfl
  have hmsr : AbsolutelyContinuousOnInterval mStar (S.r p.1 p.2) L := hms.mono (by
    rw [uIcc_of_le hrL, uIcc_of_le hLL]; exact hinterval)
  have hgs : ContinuousOn gs (Icc (S.r p.1 p.2) L) := continuousOn_const.sub
    ((continuousOn_const.mul (hmsc.mono hinterval)).div continuousOn_id
      (fun s hs => (hL₀p.trans_le (hinterval hs).1).ne'))
  have hD : AbsolutelyContinuousOnInterval dm (S.r p.1 p.2) L := hmac.sub hmsr
  have hbd : |dm L| ≤ (Ct + 4) * epsilon / L := by
    have hb := (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).2.2.2.2.1
    dsimp [dm, mr]
    rw [hright]
    have hRL := (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
    simpa only [massComparison, hRL] using hb.trans
      (div_le_div_of_nonneg_right
        (by nlinarith only [he] : Ct * epsilon ≤ (Ct + 4) * epsilon) hLp.le)
  have hYr (s) (hs : s ∈ Icc (S.r p.1 p.2) L) :
      ‖y s - yStar s‖ ≤ (Ct + 4) * epsilon / L + (64 * Cn + 1) * Nphi / s +
        (64 * Cn + 1) * Nm / s ^ 2 +
        (64 * Ce) * eta / s ^ 3 + (64 * Ce) * eta / L * Real.log (L / s) := by
    have hh := hscalarY (p.1, inv s) (hpath (inv s) (hmem s))
    rw [hrad s hs] at hh
    apply hh.trans
    gcongr <;> linarith
  have hdeq : ∀ᵐ s ∂volume.restrict (Icc (S.r p.1 p.2) L), deriv dm s =
      -(‖y s‖ ^ 2 / s) * dm s + ((Qr s ^ 2 - qStar ^ 2) / (2 * s ^ 2) +
        gs s * (starRingEnd ℂ (yStar s) * (y s - yStar s)).re +
        gs s / 2 * ‖y s - yStar s‖ ^ 2) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hdstatic := hmsd s ⟨hp.2.1.trans_lt hs.1, hs.2⟩
    have hdD := (hmd s hs).sub hdstatic
    rw [show deriv dm s = _ from hdD.deriv]
    dsimp [dm, mr, Qr, gs, y]
    linear_combination mass_difference_algebra s (S.m p.1 (inv s)) (mStar s)
      (S.Q p.1 (inv s)) qStar 1 (S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)) (yStar s)
  have hresult := hmass L₀ (S.r p.1 p.2) L epsilon eta Nphi Nm qStar dm gs Qr y yStar
    hL₀ hp.2.1 hp.2.2 he he1 heta heta1 hNp hNm hq hD hy
    (hys.mono hinterval) hgs hQr henergy hbd
    (fun s hs => ⟨(hstatic s (hinterval hs)).2.1, (hstatic s (hinterval hs)).2.2.1,
      hcharge (p.1, inv s) (hpath (inv s) (hmem s))⟩) hYr hdeq
  simpa only [dm, mr, hleft, massComparison, Real.norm_eq_abs] using hresult


end Observation
end EmcsfAcExtension.Global
