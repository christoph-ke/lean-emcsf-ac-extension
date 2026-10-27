module

public import EmcsfAcExtension.Global.Observation.WrappersComponents
public import EmcsfAcExtension.Global.Observation.WrappersMass
public import EmcsfAcExtension.Global.Observation.WrappersRadial
import Mathlib

/-! # The stopped outer comparison on the actual fields

All charge, potential, source, scalar and mass inputs are discharged from the
normalization record, constructed by the source consumer in `WrappersOuter`.
Source: charged_SF_new_version.tex:L2348–2531.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal] Improved charge and potential on the actual region under the
single temporary scalar stop. `Cp` is universal; `Cq` depends additionally
on the boundary-charge coefficient, before any fields, radii or errors. -/
theorem outer_controls_of_normalization (Kstatic : ℝ) (hK : 0 ≤ Kstatic) :
    ∃ Cp > 0, ∀ Bboundary : ℝ, 0 ≤ Bboundary → ∃ Cq > 0,
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e Ct : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    1 ≤ Lzero → Cq * eta ≤ 1 → comparisonNorm R (scalarComparison S H phiStar) ≤ 1 →
    ∀ p ∈ R, |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
      |S.A p.1 p.2| ≤ Cp / S.r p.1 p.2 ∧
      |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2) := by
  obtain ⟨Cp, hCp, hcontrols⟩ := outer_charge_potential_of_normalization Kstatic hK
  refine ⟨Cp, hCp, ?_⟩
  intro Bboundary hB
  obtain ⟨Cq, hCq, hcontrols⟩ := hcontrols Bboundary hB
  refine ⟨Cq, hCq, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Ct
  dsimp only
  intro h hLzero hsmall hstop
  rcases h.fields with ⟨cr, cn, cl, ca, cp, ct, cm, cq⟩
  have hd (p) (hp : p ∈ sidewaysTruncation S D a b Lzero L) (t) (ht : t ∈ Ioo p.2 p.1) :=
    h.equations (p.1,t) ((sidewaysTruncation_paths (h.triangles p hp)).2 t (Ioo_subset_Icc_self ht))
  exact hcontrols S D e eta a b Lzero L qStar H phiStar
    (zero_lt_one.trans_le hLzero) (hLzero.trans h.ordered) h.reference_charge h.scale hsmall hstop
    (fun p hp => (h.static_bounds (S.r p.1 p.2) hp.2).2.2.2.1)
    h.triangles cr cl cn cm cq ca cp ct
    (fun p hp => ⟨(by linarith only [(h.box p hp).2.1.1]),
      abs_le.mpr ⟨(h.box p hp).1.1, by linarith only [(h.box p hp).1.2]⟩, (h.box p hp).2.2⟩)
    (fun p hp t ht => ⟨(hd p hp t ht).2.1, (hd p hp t ht).2.2.2.1,
      (hd p hp t ht).2.2.2.2.1, (hd p hp t ht).2.2.1, (hd p hp t ht).2.2.2.2.2.1⟩)
    (fun t ht => ⟨(h.boundary t ht).1, (h.boundary t ht).2.2.2.2.2.1,
      (h.boundary t ht).2.2.2.2.2.2⟩)

/-- [internal] The complete stopped outer conclusions, including the separate
components and both regional polynomial inequalities. Only a temporary scalar
bound and arbitrary numerical upper envelopes are tested in this conclusion;
there is no added premise on a physical source theorem. -/
@[expose] noncomputable def outerStopped (Kstatic Cp Cq Cn Ce Cnc Cec CnM CbM CeM Cem : ℝ)
    (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ) (phiStar yStar : ℝ → ℂ)
    (mStar : ℝ → ℝ) (a b Lzero L epsilon eta qStar e Ct : ℝ) : Prop :=
  let R := sidewaysTruncation S D a b Lzero L
  ∀ Nphi Nm : ℝ, 0 ≤ Nphi → Nphi ≤ 1 → 0 ≤ Nm →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal Nphi →
    comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal Nm →
    ((∀ p ∈ R, ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1) ∧
      comparisonNorm R (massComparison S mStar) ≤ 4) ∧
    (∀ p ∈ R, |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
      |S.A p.1 p.2| ≤ Cp / S.r p.1 p.2 ∧
      |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2)) ∧
    (∀ p ∈ R, outerComponentsAt Cnc Cec S H phiStar yStar mStar qStar e eta L Nphi Nm p.1 p.2) ∧
    (∀ p ∈ R, ‖outerWv S H phiStar yStar p.1 p.2‖ ≤ epsilon / (2 * L) +
      8 * (Cn * (Nphi + Nm)) / S.r p.1 p.2 ^ 2 + 8 * (Ce * eta) / S.r p.1 p.2 ^ 3 +
        8 * (Ce * eta) / L * Real.log (L / S.r p.1 p.2)) ∧
    comparisonNorm R (scalarComparison S H phiStar) ≤
      ENNReal.ofReal ((Ct + 4) * epsilon + 64 * (Cn * (Nphi + Nm)) / Lzero + 96 * (Ce * eta)) ∧
    (∀ p ∈ R, ‖S.theta p.1 p.2 / S.lam p.1 p.2 - yStar (S.r p.1 p.2)‖ ≤
      4 * epsilon / L + (64 * Cn + 1) * Nphi / S.r p.1 p.2 +
        64 * Cn * Nm / S.r p.1 p.2 ^ 2 + 64 * Ce * eta / S.r p.1 p.2 ^ 3 +
          64 * Ce * eta / L * Real.log (L / S.r p.1 p.2)) ∧
    comparisonNorm R (massComparison S mStar) ≤
      ENNReal.ofReal ((CbM * epsilon + CeM * eta) / Lzero +
        (CnM / Lzero) * (Nphi + Nphi ^ 2) + (CnM / Lzero ^ 2) * Nm + (CnM / Lzero ^ 3) * Nm ^ 2) ∧
    outerElectricMass S D a b Lzero L qStar eta Cq Cem

/-- [internal] Assemble the stopped conclusions without an estimate premise.
Neutral constants depend only on `Kstatic`; subsequent coefficients may depend
on `Ct,Bboundary`, and are uniform in all fields, radii, amplitudes and errors. -/
theorem outer_stopped_of_normalization (Kstatic : ℝ) (hK : 0 ≤ Kstatic) :
    ∃ Cp Cn Cnc CnM Cem : ℝ, 0 < Cp ∧ 0 < Cn ∧ 0 < Cnc ∧ 0 < CnM ∧ 0 < Cem ∧
    ∀ Ct Bboundary : ℝ, 0 ≤ Ct → 0 ≤ Bboundary →
    ∃ Cq Ce Cec CbM CeM : ℝ,
      0 < Cq ∧ 0 < Ce ∧ 0 < Cec ∧ 0 < CbM ∧ 0 < CeM ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e : ℝ),
    OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    1 ≤ Lzero → Cq * eta ≤ 1 →
    outerStopped Kstatic Cp Cq Cn Ce Cnc Cec CnM CbM CeM Cem
      S D H phiStar yStar mStar a b Lzero L epsilon eta qStar e Ct := by
  obtain ⟨Cp, hCp, hcontrols⟩ := outer_controls_of_normalization Kstatic hK
  obtain ⟨Cn, hCn, hscalar⟩ := outer_scalar_of_normalization Kstatic hK
  obtain ⟨Cnc, hCnc, hcomp⟩ := outer_components_of_normalization Kstatic Cp hK hCp.le
  obtain ⟨CnM, hCnM, hmass⟩ := outer_mass_of_normalization Kstatic Cn hK hCn.le
  obtain ⟨Cem, hCem, hem⟩ := outer_electric_mass_of_normalization
  refine ⟨Cp, Cn, Cnc, CnM, Cem, hCp, hCn, hCnc, hCnM, hCem, ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨CqP, hCqP, hcontrols⟩ := hcontrols Bboundary hB
  obtain ⟨Ce, CqS, hCe, hCqS, hscalar⟩ := hscalar Bboundary hB
  let Cq := max CqP CqS
  have hCq : 0 < Cq := hCqP.trans_le (le_max_left _ _)
  obtain ⟨Cec, hCec, hcomp⟩ := hcomp Cq hCq.le
  obtain ⟨CbM, CeM, hCbM, hCeM, hmass⟩ := hmass Ct Ce Cq hCt hCe.le hCq.le
  refine ⟨Cq, Ce, Cec, CbM, CeM, hCq, hCe, hCec, hCbM, hCeM, ?_⟩
  intro S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e h hLzero hsmall
    Nphi Nm hNp hstop hNm hw hm
  let R := sidewaysTruncation S D a b Lzero L
  have hstopNorm : comparisonNorm R (scalarComparison S H phiStar) ≤ 1 :=
    hw.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hstop)
  have hcon := hcontrols S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Ct h hLzero
    ((mul_le_mul_of_nonneg_right (le_max_left _ _) h.errors.2.1).trans hsmall) hstopNorm
  have controls (p) (hp : p ∈ R) : |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
      |S.A p.1 p.2| ≤ Cp / S.r p.1 p.2 ∧
      |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2) :=
    ⟨(hcon p hp).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h.errors.2.1), (hcon p hp).2⟩
  have charge (p) (hp : p ∈ R) : |S.Q p.1 p.2| ≤ 2 ∧ |S.Q p.1 p.2 - qStar| ≤ Cq * eta :=
    ⟨(controls p hp).2.1, (controls p hp).1⟩
  have scalar := hscalar Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
    h hLzero hCt ((mul_le_mul_of_nonneg_right (le_max_right _ _) h.errors.2.1).trans hsmall)
    hNp hstop hNm hw hm
  have bootstrap : (∀ p ∈ R, ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1) ∧
      comparisonNorm R (massComparison S mStar) ≤ 4 := by
    obtain ⟨K, _hK, hb⟩ := outer_bootstrap_box_of_normalization Kstatic hK
    -- The landed helper uses the explicit witness `Kstatic+1`; reproduce its two-line bound.
    constructor
    · intro p hp
      have hh := norm_le_of_comparisonNorm_le (by norm_num : (0 : ℝ) ≤ 1) hp
        (by simpa only [ENNReal.ofReal_one] using hstopNorm)
      calc
        _ = ‖scalarComparison S H phiStar p.1 p.2 + (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by
          rw [scalarComparison, sub_add_cancel]
        _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ + ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ :=
            norm_add_le _ _
        _ ≤ Kstatic + 1 := by linarith only [hh, (h.static_bounds (S.r p.1 p.2) hp.2).2.2.2.1]
    · exact (hb S R H phiStar mStar hstopNorm
        (fun p hp => (h.static_bounds (S.r p.1 p.2) hp.2).2.2.2.1)
        (fun p hp => (h.box p hp).2.2.1)
        (fun p hp => (h.static_bounds (S.r p.1 p.2) hp.2).1)).2
  exact ⟨bootstrap, controls,
    hcomp S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm Bboundary Ct
      h hLzero hstopNorm (fun p hp => ⟨(controls p hp).1, (controls p hp).2.1, (controls p
          hp).2.2.2⟩)
      hNp hNm hw hm,
    scalar.2.1, scalar.2.2.1, scalar.2.2.2,
    hmass S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm Bboundary
      h hLzero hNp hNm charge scalar.2.2.2,
    hem Kstatic Ct Bboundary a b Lzero L epsilon eta qStar e Cq S D H P phiStar yStar mStar
      (zero_lt_one.trans_le hLzero) hCq.le h charge⟩

end EmcsfAcExtension.Global.Observation
