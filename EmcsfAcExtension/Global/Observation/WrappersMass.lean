module

public import EmcsfAcExtension.Global.Observation.WrappersScalar
import EmcsfAcExtension.Global.Observation.OuterMass
import Mathlib

/-! # The outer regional mass polynomial

The mass difference is the actual normalized mass minus the same radial
reference. Every radius inverse stays in its endpoint's triangle.
Source: charged_SF_new_version.tex:L2497–2531.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] Integrate the actual mass equation and take the regional norm.
The neutral coefficient depends only on `Kstatic,Cn`; boundary and electric
coefficients are fixed next, before fields, radii, coupling and errors.
Its scalar input is discharged by `outer_scalar_of_normalization`. -/
theorem outer_mass_of_normalization (Kstatic Cn : ℝ) (hKs : 0 ≤ Kstatic) (hCn : 0 ≤ Cn) :
    ∃ CnM : ℝ, 0 < CnM ∧ ∀ Ct Ce B : ℝ,
    0 ≤ Ct → 0 ≤ Ce → 0 ≤ B → ∃ CbM CeM : ℝ, 0 < CbM ∧ 0 < CeM ∧
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
  obtain ⟨CnM, hCnM, hmass⟩ := co_outer_mass_of_scalar_estimate Kstatic (64 * Cn + 1) hKs
      (by positivity)
  refine ⟨CnM, hCnM, ?_⟩
  intro Ct Ce B hCt hCe hB
  obtain ⟨CbM, CeM, hCbM, hCeM, hmass⟩ := hmass (Ct + 4) (64 * Ce) B (by positivity) (by positivity)
      hB
  refine ⟨CbM, CeM, hCbM, hCeM, ?_⟩
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
  obtain ⟨inv, hrL, hci, hmem, hrad, hleft, hright, hdi, hy, hmr, hQr, hmd, hmac, hradbox, henergy⟩
      :=
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
      (div_le_div_of_nonneg_right (by nlinarith only [he] : Ct * epsilon ≤ (Ct + 4) * epsilon)
          hLp.le)
  have hYr (s) (hs : s ∈ Icc (S.r p.1 p.2) L) :
      ‖y s - yStar s‖ ≤ (Ct + 4) * epsilon / L + (64 * Cn + 1) * Nphi / s + (64 * Cn + 1) * Nm / s ^
          2 +
        (64 * Ce) * eta / s ^ 3 + (64 * Ce) * eta / L * Real.log (L / s) := by
    have hh := hscalarY (p.1, inv s) (hpath (inv s) (hmem s))
    rw [hrad s hs] at hh
    apply hh.trans
    gcongr <;> linarith
  have hdeq : ∀ᵐ s ∂volume.restrict (Icc (S.r p.1 p.2) L), deriv dm s =
      -(‖y s‖ ^ 2 / s) * dm s + ((Qr s ^ 2 - qStar ^ 2) / (2 * s ^ 2) +
        gs s * (starRingEnd ℂ (yStar s) * (y s - yStar s)).re + gs s / 2 * ‖y s - yStar s‖ ^ 2) :=
            by
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

end EmcsfAcExtension.Global.Observation
