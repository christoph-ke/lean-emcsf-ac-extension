module

public import EmcsfAcExtension.Global.Observation.IncomingTrace
import EmcsfAcExtension.Global.Observation.OuterClosure
import EmcsfAcExtension.Global.Observation.WaveDifference
import Mathlib

/-! # The outgoing scalar error and charge in the outer normalization

The exact incoming transport of the outgoing derivative gives the
uniform outgoing-ratio error needed on the constructed inner cylinder.
Source: charged_SF_new_version.tex:L2481–2495, L2541–2583; approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Discharge the source and transport inputs of the outgoing ratio estimate
from the actual outer normalization record. The scalar and mass suprema
remain inputs of this helper; its closure consumer derives both from
the landed outer comparison. Constants are selected after `Kstatic`,
then `Bboundary`, before all fields, radii, backgrounds and errors. -/
theorem outer_outgoing_of_raw_outer_estimates (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ Bboundary : ℝ, 0 ≤ Bboundary →
    ∃ Ce Cq : ℝ, 0 < Ce ∧ 0 < Cq ∧
    ∀ (Ct : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e Nphi Nm : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    1 ≤ Lzero → 0 ≤ Ct → Cq * eta ≤ 1 → 0 ≤ Nphi → Nphi ≤ 1 → 0 ≤ Nm →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal Nphi →
    comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal Nm →
    ∀ p ∈ R, |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧
      ‖S.theta p.1 p.2 / S.lam p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
        4 * epsilon / L + (64 * Cn + 1) * Nphi / S.r p.1 p.2 +
          64 * Cn * Nm / S.r p.1 p.2 ^ 2 + 64 * Ce * eta / S.r p.1 p.2 ^ 3 +
          64 * Ce * eta / L * Real.log (L / S.r p.1 p.2) := by
  obtain ⟨_Cp, Cn, _hCp, hCn, hsources⟩ := outer_sources_of_normalization Kstatic hKs
  refine ⟨Cn, hCn, ?_⟩
  intro Bboundary hB
  obtain ⟨Cq, Ce, hCq, hCe, hsource⟩ := hsources Bboundary hB
  refine ⟨Ce, Cq, hCe, hCq, ?_⟩
  intro Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
  dsimp only
  intro h hLzero _hCt hsmall hNp hstop hNm hw hmBound
  let R := sidewaysTruncation S D a b Lzero L
  let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  let k := fun u v => (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
  let wV := fun u v => (S.lam u v : ℂ) *
    (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v
  let source := fun u v =>
    -(((-S.nu u v) * S.lam u v * k u v / S.r u v ^ 2 : ℝ) : ℂ) *
      scalarComparison S H phiStar u v +
    (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) * yStar (S.r u v) *
      ((k u v - ks (S.r u v) : ℝ) : ℂ) -
    I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) *
      (H + (phiStar (S.r u v) + yStar (S.r u v))) +
    I * ((e * (-S.nu u v) * S.lam u v * S.Q u v /
      ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
      (shiftedRphi S H u v + (S.r u v : ℂ) * H)
  rcases h.fields with ⟨hr, hnu, hlam, hA, hphi, htheta, hm, hQ⟩
  have hLp : 0 < Lzero := zero_lt_one.trans_le hLzero
  have hL : 1 ≤ L := hLzero.trans h.ordered
  have hSsmall : Cq * eta ≤ 1 := hsmall
  have hsec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :=
    continuousOn_outgoing_of_subtriangle hc (h.triangles p hp)
  have hstat (p) (hp : p ∈ R) := h.static_bounds (S.r p.1 p.2) hp.2
  have hbox (p) (hp : p ∈ R) : 0 < S.lam p.1 p.2 ∧ |S.nu p.1 p.2| ≤ 1 / 2 ∧
      S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2 := by
    have hb := h.box p hp
    exact ⟨(by norm_num : (0 : ℝ) < 1 / 8).trans_le hb.2.1.1,
      abs_le.mpr ⟨hb.1.1, by linarith only [hb.1.2]⟩, hb.2.2⟩
  have hdout (p) (hp : p ∈ R) (t) (ht : t ∈ Ioo p.2 p.1) :=
    h.equations (p.1, t) ((sidewaysTruncation_paths (h.triangles p hp)).2 t
      (Ioo_subset_Icc_self ht))
  have hsources (P M : ℝ) (hP : 0 ≤ P) (hP1 : P ≤ 1) (hM : 0 ≤ M)
      (hwP : ∀ p ∈ R, ‖scalarComparison S H phiStar p.1 p.2‖ ≤ P)
      (hmM : ∀ p ∈ R, ‖massComparison S mStar p.1 p.2‖ ≤ M) :=
    hsource S D e eta a b Lzero L qStar P M H phiStar yStar mStar hLzero h.ordered
      h.errors.2.1 h.reference_charge h.scale hSsmall hP hP1 hM hwP hmM
      (fun p hp => ⟨(hstat p hp).2.2.2.1, (hstat p hp).2.1,
        (hstat p hp).2.2.2.2.1, (hstat p hp).2.2.2.2.2⟩)
      h.triangles hr hlam hnu hm hQ hA hphi htheta
      (fun p hp => ⟨(hbox p hp).1, (h.box p hp).2.1.2,
        ⟨(h.box p hp).1.1, (h.box p hp).1.2.trans (by norm_num)⟩, (h.box p hp).2.2⟩)
      (fun p hp t ht => ⟨(hdout p hp t ht).2.1, (hdout p hp t ht).2.2.2.1,
        (hdout p hp t ht).2.2.2.2.1, (hdout p hp t ht).2.2.1,
        (hdout p hp t ht).2.2.2.2.2.1⟩)
      (fun t ht => ⟨(h.boundary t ht).1, (h.boundary t ht).2.2.2.2.2.1,
        (h.boundary t ht).2.2.2.2.2.2⟩)
  have hsActual := hsources Nphi Nm hNp hstop hNm
    (fun p hp => norm_le_of_comparisonNorm_le hNp hp hw)
    (fun p hp => norm_le_of_comparisonNorm_le hNm hp hmBound)
  have hmsc : ContinuousOn mStar (Icc Lzero L) := by
    simpa only [uIcc_of_le h.ordered] using h.static_mass_ac.continuousOn
  have hks : ContinuousOn ks (Icc Lzero L) := by
    have hc : ContinuousOn (fun s => 2 * mStar s / s) (Icc Lzero L) :=
      (continuousOn_const.mul hmsc).div continuousOn_id (fun s hs => (hLp.trans_le hs.1).ne')
    exact (hc.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hLp.trans_le hs.1).ne'))).div (continuousOn_const.sub hc)
      (fun s hs => by linarith only [(h.static_bounds s hs).2.2.2.2.2])
  have hsectionIn {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :
      ContinuousOn (fun u => f u p.2) (Icc p.2 p.1) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => h.triangles p hp (sidewaysTriangle_incoming hu))
  have htransport (p) (hp : p ∈ R) := co_wv_transport_of_normalization H phiStar yStar ks
    hp.1.2.2.1 (hsectionIn hr p hp) (hsectionIn hnu p hp) (hsectionIn hlam p hp)
    (hsectionIn hm p hp) (hsectionIn hQ p hp) (hsectionIn hA p hp)
    (hsectionIn hphi p hp) (hsectionIn htheta p hp)
    (fun u hu => (hLp.trans_le (h.triangles p hp (sidewaysTriangle_incoming hu)).2.1).ne')
    (fun u hu => by linarith only [(h.box (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming hu))).2.2.2])
    (h.static_continuous.1.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (h.static_continuous.2.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (hks.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.2.1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.2.2)
    (fun u hu => (h.static_equations (S.r u p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu))).2).2.1)
  intro p hp
  have ht := htransport p hp
  have hboundary := h.boundary p.2 (h.triangles p hp
      (sidewaysTriangle_incoming ⟨le_rfl, hp.1.2.2.1⟩))
  have hb := Observation.outer_boundary_difference_data_of_normalization S H P phiStar yStar
      (hLp.trans_le h.ordered) hboundary.1 hboundary.2.1 h.static_boundary.1 h.static_boundary.2
      hboundary.2.2.1 hboundary.2.2.2.1
  have hV : ‖wV p.1 p.2‖ ≤ epsilon / (2 * L) +
      8 * (Cn * (Nphi + Nm)) / S.r p.1 p.2 ^ 2 +
      8 * (Ce * eta) / S.r p.1 p.2 ^ 3 +
      8 * (Ce * eta) / L * Real.log (L / S.r p.1 p.2) := by
    apply incoming_comparison_bound hp.1.2.2.1 hLp
      (fun u hu => (h.equations (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).1)
      (hsectionIn hnu p hp) (fun u hu => (h.triangles p hp (sidewaysTriangle_incoming hu)).2)
      (fun u hu => (h.box (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).1.2)
      hboundary.1 (by positivity : 0 ≤ Cn * (Nphi + Nm)) (mul_nonneg hCe.le h.errors.2.1)
      ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2
    · simpa only [wV, hb.2.1] using hb.2.2
    · intro u hu
      convert (hsActual (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).2.2 using 1
      ring
  refine ⟨(hsActual p hp).1, ?_⟩
  exact co_outer_y_of_incoming_estimate Cn Ce hCn.le (hLzero.trans hp.2.1)
    (h.box p hp).2.1.1 hNp (norm_le_of_comparisonNorm_le hNp hp hw) rfl hV

/-- [internal]
The uniform outgoing and charge bounds on the actual outer region, with
both comparison suprema discharged by the landed outer closure. The
cutoff depends only on the static bound, and the other coefficients
only on that bound and the displayed boundary constants, uniformly in
all fields, backgrounds, scales, couplings and errors. -/
theorem outer_outgoing_of_normalization (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin > 0, ∀ Ct Bboundary : ℝ, 0 ≤ Ct → 0 ≤ Bboundary →
    ∃ CB CE Cq Ctheta Cmass : ℝ,
      0 < CB ∧ 0 < CE ∧ 0 < Cq ∧ 0 < Ctheta ∧ 0 < Cmass ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e : ℝ),
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    Lmin ≤ Lzero → 4 * (CB * epsilon + CE * eta) ≤ 1 / 2 → Cq * eta ≤ 1 →
    ∀ p ∈ sidewaysTruncation S D a b Lzero L,
      |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧
      ‖S.theta p.1 p.2 / S.lam p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
        Ctheta * (epsilon + eta) ∧
      |S.m p.1 p.2 - mStar (S.r p.1 p.2)| ≤ Cmass * (epsilon + eta) := by
  obtain ⟨Lmin, Cm, hLmin, hCm, houter⟩ := outer_comparison_of_normalization Kstatic hKs
  obtain ⟨Cn, hCn, hraw⟩ := outer_outgoing_of_raw_outer_estimates Kstatic hKs
  refine ⟨max Lmin 1, lt_of_lt_of_le hLmin (le_max_left _ _), ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨CB, CE, CqO, hCB, hCE, hCqO, houter⟩ := houter Ct Bboundary hCt hB
  obtain ⟨Ce, CqI, hCe, hCqI, hraw⟩ := hraw Bboundary hB
  let Ctheta := 4 + (((64 * Cn + 1) * 4 + 64 * Cn * Cm) * (CB + CE) + 128 * Ce)
  let Cmass := Cm * (CB + CE)
  refine ⟨CB, CE, max CqO CqI, Ctheta, Cmass, hCB, hCE,
    lt_of_lt_of_le hCqO (le_max_left _ _), by dsimp [Ctheta]; positivity,
    by dsimp [Cmass]; positivity, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e h hLzero hsmall hcharge p hp
  let R := sidewaysTruncation S D a b Lzero L
  let Nphi := 4 * (CB * epsilon + CE * eta)
  let Nm := Cm * (CB * epsilon + CE * eta) / Lzero
  have hL1 : 1 ≤ Lzero := (le_max_right _ _).trans hLzero
  have he := h.errors.1.1
  have heta := h.errors.2.1
  have hNp : 0 ≤ Nphi := by dsimp [Nphi]; positivity
  have hNm : 0 ≤ Nm := by dsimp [Nm]; positivity
  have hO : CqO * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) heta).trans hcharge
  have hI : CqI * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) heta).trans hcharge
  have ho := houter S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e
    ((le_max_left _ _).trans hLzero) h.ordered he h.errors.1.2 heta h.errors.2.2
    hsmall hO h.reference_charge h.scale h.compact h.fields h.static_mass_ac
    h.static_continuous.1 h.static_continuous.2 h.static_boundary.1 h.static_boundary.2
    h.static_equations h.static_bounds h.base h.triangles h.box h.equations h.boundary
  have hi := hraw Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
    h hL1 hCt hI hNp (hsmall.trans (by norm_num)) hNm ho.1 ho.2 p hp
  have hr : 1 ≤ S.r p.1 p.2 := hL1.trans hp.2.1
  have hrem := incoming_remainder_of_outer hr hp.2.2 hL1 hCB.le hCE.le hCm.le
    (show 0 ≤ 8 * Cn by positivity) (show 0 ≤ 8 * Ce by positivity)
    (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 0 by norm_num) he heta
  have hrest : (64 * Cn + 1) * Nphi / S.r p.1 p.2 +
      64 * Cn * Nm / S.r p.1 p.2 ^ 2 + 64 * Ce * eta / S.r p.1 p.2 ^ 3 +
      64 * Ce * eta / L * Real.log (L / S.r p.1 p.2) ≤
      (Ctheta - 4) * (epsilon + eta) := by
    convert hrem using 1 <;> dsimp [Nphi, Nm, Ctheta] <;> ring
  have hfirst : 4 * epsilon / L ≤ 4 * (epsilon + eta) :=
    (div_le_self (by positivity) (hL1.trans h.ordered)).trans (by linarith only [heta])
  have hm := norm_le_of_comparisonNorm_le hNm hp ho.2
  have herr : CB * epsilon + CE * eta ≤ (CB + CE) * (epsilon + eta) := by
    nlinarith only [mul_nonneg hCB.le heta, mul_nonneg hCE.le he]
  refine ⟨hi.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) heta), ?_, ?_⟩
  · linarith only [hi.2, hrest, hfirst]
  · have hmb := (div_le_self (by positivity : 0 ≤ Cm * (CB * epsilon + CE * eta)) hL1).trans
      (mul_le_mul_of_nonneg_left herr hCm.le)
    simpa only [massComparison, Real.norm_eq_abs, Cmass, mul_assoc] using hm.trans hmb

end EmcsfAcExtension.Global.Observation
