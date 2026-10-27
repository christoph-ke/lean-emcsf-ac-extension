module

public import EmcsfAcExtension.Global.Observation.WrappersExact
import Mathlib

/-! # The stopped outer scalar estimate on normalized fields

The literal source, transport, outgoing derivative and boundary data are
all derived here. Source: charged_SF_new_version.tex:L2476–2495.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] The actual stopped scalar supremum and outgoing derivative
bounds. The neutral coefficient depends only on `Kstatic`; electric and charge
coefficients additionally depend on the boundary-charge coefficient, before
all fields, radii, backgrounds and errors. -/
theorem outer_scalar_of_normalization (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
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
    (∀ p ∈ R, |S.Q p.1 p.2 - qStar| ≤ Cq * eta) ∧
    (∀ p ∈ R, ‖outerWv S H phiStar yStar p.1 p.2‖ ≤ epsilon / (2 * L) +
      8 * (Cn * (Nphi + Nm)) / S.r p.1 p.2 ^ 2 + 8 * (Ce * eta) / S.r p.1 p.2 ^ 3 +
        8 * (Ce * eta) / L * Real.log (L / S.r p.1 p.2)) ∧
    comparisonNorm R (scalarComparison S H phiStar) ≤
      ENNReal.ofReal ((Ct + 4) * epsilon + 64 * (Cn * (Nphi + Nm)) / Lzero + 96 * (Ce * eta)) ∧
    (∀ p ∈ R, ‖S.theta p.1 p.2 / S.lam p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
      4 * epsilon / L + (64 * Cn + 1) * Nphi / S.r p.1 p.2 +
        64 * Cn * Nm / S.r p.1 p.2 ^ 2 + 64 * Ce * eta / S.r p.1 p.2 ^ 3 +
          64 * Ce * eta / L * Real.log (L / S.r p.1 p.2)) := by
  obtain ⟨_Cp, Cn, _hCp, hCn, hsources⟩ := outer_sources_of_normalization Kstatic hKs
  refine ⟨Cn, hCn, ?_⟩
  intro Bboundary hB
  obtain ⟨Cq, Ce, hCq, hCe, hsource⟩ := hsources Bboundary hB
  refine ⟨Ce, Cq, hCe, hCq, ?_⟩
  intro Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
  dsimp only
  intro h hLzero hCt hsmall hNp hstop hNm hw hmBound
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
  refine ⟨fun p hp => (hsActual p hp).1, ?_⟩
  have he := outer_exact_of_normalization hLp h
  apply co_outer_sup_of_source_envelope Ct Cn Ce hCt hCn.le hCe.le wV source
    (fun u v => e * S.A u v) hLzero le_rfl hNp hNm h.errors.1.1 h.errors.2.1
    h.triangles (fun p hp => (h.equations p hp).1)
    (fun p hp => (h.equations p hp).2.1)
    (fun p hp => ⟨hsectionIn hnu p hp, hsec hlam p hp⟩)
    (fun p hp => ⟨(h.box p hp).1.2, (h.box p hp).2.1.1⟩)
    (fun t ht => ?_)
    (fun p hp => (htransport p hp).2.2.2.1)
    (fun p hp => (htransport p hp).2.2.2.2.1)
    (fun p hp => (htransport p hp).2.2.2.2.2.1)
    (fun p hp => (htransport p hp).2.2.2.2.2.2)
    (fun p hp => (he.1 p hp).2.1)
    (fun p hp => ?_)
    (fun p hp => norm_le_of_comparisonNorm_le hNp hp hw) (fun _ _ => rfl)
    (fun p hp => (hsActual p hp).2.2)
  · have hb := h.boundary t ht
    have hh := outer_boundary_difference_data_of_normalization S H P phiStar yStar
      (hLp.trans_le h.ordered) hb.1 hb.2.1 h.static_boundary.1 h.static_boundary.2
      hb.2.2.1 hb.2.2.2.1
    refine ⟨hb.1, hh.1, ?_⟩
    simpa only [wV, hh.2.1] using hh.2.2
  · have cstatic := (h.static_continuous.1.add h.static_continuous.2).comp (hsec hr p hp)
      (fun t ht => (sidewaysTruncation_paths (h.triangles p hp)).2 t ht |>.2)
    exact (((Complex.continuous_ofReal.comp_continuousOn (hsec hlam p hp)).mul
      (((hsec hphi p hp).sub continuousOn_const).sub cstatic)).add
        (hsec htheta p hp)).intervalIntegrable_of_Icc hp.1.2.2.1

end EmcsfAcExtension.Global.Observation
