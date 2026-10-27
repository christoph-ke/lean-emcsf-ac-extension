module

public import EmcsfAcExtension.Global.Observation.InnerClosure

public import EmcsfAcExtension.Global.Defs.Observation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Absorbing the charged comparison error at a strict barrier

The stopping radius and strict reference margin are fixed before the charged
and boundary tolerances. These finite-dimensional estimates do not assume a
regular center for a static reference. Source: `charged_SF_new_version.tex:L2740–L2780`
and the observation synthesis in the approved internal project record.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Mass closeness through a fixed positive stopping radius transfers either
strict reference violation to the actual mass or gap. There are no chosen
constants. The comparison consumer supplies the actual and reference masses
at the same radius. -/
theorem strict_barrier_contradiction_of_mass_close
    {δ rstar γ r m mstar : ℝ}
    (hrstar : 0 < rstar) (hγ : 0 < γ) (hr : rstar ≤ r)
    (hm : 0 ≤ m) (hgap : δ ≤ 1 - 2 * m / r)
    (hclose : |m - mstar| < min γ (rstar * γ / 2))
    (hbarrier : mstar ≤ -γ ∨ 1 - 2 * mstar / r ≤ δ - γ) : False := by
  have hrpos : 0 < r := hrstar.trans_le hr
  have hdiff : m - mstar ≤ |m - mstar| := le_abs_self _
  rcases hbarrier with hmass | hgapstar
  · have hsmall := hclose.trans_le (min_le_left _ _)
    linarith only [hm, hmass, hdiff, hsmall]
  · have hsmall := hclose.trans_le (min_le_right _ _)
    have hreverse : mstar - m ≤ |m - mstar| := by
      simpa only [abs_sub_comm] using le_abs_self (mstar - m)
    have hrad : rstar * γ ≤ r * γ := mul_le_mul_of_nonneg_right hr hγ.le
    have hratio : 2 * (mstar - m) / r < γ := by
      apply (div_lt_iff₀ hrpos).mpr
      nlinarith only [hreverse, hsmall, hrad]
    have hid : 1 - 2 * m / r = 1 - 2 * mstar / r + 2 * (mstar - m) / r := by
      ring
    linarith only [hgap, hgapstar, hratio, hid]

/-- [internal]
The two errors requested at `charged_SF_new_version.tex:L2750–L2779` fit inside the
strict mass and gap margins. The common radius and violation precede both
errors; the coefficient is the already fixed comparison coefficient. -/
theorem mass_error_lt_barrier_of_tolerances {C ε η rstar γ : ℝ}
    (hγ : 0 < γ) (hrstar : 0 < rstar)
    (hε : C * ε < min (γ / 4) (rstar * γ / 8))
    (hη : C * η < min (γ / 4) (rstar * γ / 8)) :
    C * (ε + η) < min γ (rstar * γ / 2) := by
  have hεm := hε.trans_le (min_le_left _ _)
  have hηm := hη.trans_le (min_le_left _ _)
  have hεg := hε.trans_le (min_le_right _ _)
  have hηg := hη.trans_le (min_le_right _ _)
  apply lt_min
  · nlinarith only [hεm, hηm, hγ]
  · have hp := mul_pos hrstar hγ
    nlinarith only [hεg, hηg, hp]

/-- [internal]
For fixed positive stopping radius, violation margin, and nonnegative
comparison coefficient, choose the physical charged tolerance first and
then the boundary tolerance. Both may also satisfy independently prescribed
positive caps. All witnesses precede the actual mass, radius, and errors.
The window and comparison consumers must supply those fixed parameters. -/
theorem strict_barrier_tolerances {C rstar γ ηcap εcap : ℝ}
    (hC : 0 ≤ C) (hrstar : 0 < rstar) (hγ : 0 < γ)
    (hηcap : 0 < ηcap) (hεcap : 0 < εcap) :
    ∃ ηstar > 0, ηstar ≤ ηcap ∧ ∃ εstar > 0, εstar ≤ εcap ∧
      ∀ (δ r m mstar ε η : ℝ), ε ≤ εstar → η ≤ ηstar →
        rstar ≤ r → 0 ≤ m → δ ≤ 1 - 2 * m / r →
        |m - mstar| ≤ C * (ε + η) →
        (mstar ≤ -γ ∨ 1 - 2 * mstar / r ≤ δ - γ) → False := by
  let margin := min (γ / 4) (rstar * γ / 8)
  have hmargin : 0 < margin := lt_min (by positivity) (by positivity)
  let tol := margin / (2 * (C + 1))
  have htol : 0 < tol := div_pos hmargin (by positivity)
  have hCt : C * tol < margin := by
    dsimp only [tol]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))).mpr
    nlinarith only [hmargin, hC, mul_nonneg hC hmargin.le]
  refine ⟨min ηcap tol, lt_min hηcap htol, min_le_left _ _,
    min εcap tol, lt_min hεcap htol, min_le_left _ _, ?_⟩
  intro δ r m mstar ε η hε hη hr hm hg hclose hbarrier
  have hεsmall : C * ε < margin :=
    (mul_le_mul_of_nonneg_left (hε.trans (min_le_right _ _)) hC).trans_lt hCt
  have hηsmall : C * η < margin :=
    (mul_le_mul_of_nonneg_left (hη.trans (min_le_right _ _)) hC).trans_lt hCt
  exact strict_barrier_contradiction_of_mass_close hrstar hγ hr hm hg
    (hclose.trans_lt (mass_error_lt_barrier_of_tolerances hγ hrstar hεsmall hηsmall)) hbarrier

/-- [internal]
The landed inner comparison record discharges the mass-comparison input
of the strict barrier contradiction. The comparison coefficient and its
smallness threshold are selected first, then the charged tolerance and
boundary tolerance, before every member-dependent cutoff and all actual
fields, couplings, backgrounds, errors and test points. The remaining
record is the exact normalization interface of internal project record; no comparison
estimate, Volterra inequality or scalar stop is assumed. -/
theorem strict_barrier_contradiction_of_inner_normalization
    {rStar Lzero delta c K G Qmax Cscalar Bcharge Amax γ ηcap εcap : ℝ}
    (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hc : 0 < c)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hQmax : 0 ≤ Qmax) (hCs : 0 ≤ Cscalar)
    (hBq : 0 ≤ Bcharge) (hAm : 0 ≤ Amax) (hγ : 0 < γ)
    (hηcap : 0 < ηcap) (hεcap : 0 < εcap)
    (Ctheta Cmass Cxi : ℝ) (hCt : 0 ≤ Ctheta) (hCm : 0 ≤ Cmass) (hCx : 0 ≤ Cxi) :
    ∃ ηstar > 0, ηstar ≤ ηcap ∧ ∃ εstar > 0, εstar ≤ εcap ∧
    ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
      (yStar : ℝ → ℂ) (mStar : ℝ → ℝ) (a b qStar e epsilon eta δgap : ℝ),
    rStar ≤ rho → rho ≤ Lzero → 0 ≤ epsilon → epsilon ≤ εstar → eta ≤ ηstar →
    InnerComparisonData rho Lzero delta c K G Qmax Cscalar Bcharge Amax
      S D H yStar mStar a b qStar e eta (Ctheta * (epsilon + eta))
        (Cmass * (epsilon + eta)) (Cxi * (epsilon + eta)) →
    ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
      δgap ≤ 1 - S.mu p.1 p.2 →
      (mStar (S.r p.1 p.2) ≤ -γ ∨
        1 - 2 * mStar (S.r p.1 p.2) / S.r p.1 p.2 ≤ δgap - γ) → False := by
  obtain ⟨C, hC, sigma, hsigma, hcomparison⟩ := inner_comparison_closure_of_normalization
    hrStar hLzero hdelta hc hK hG hQmax hCs hBq hAm Ctheta Cmass Cxi hCt hCm hCx
  obtain ⟨ηstar, hηstar, hηcap', εstar, hεstar, hεcap', hcontradict⟩ :=
    strict_barrier_tolerances hC.le hrStar hγ (lt_min hηcap (half_pos hsigma))
      (lt_min hεcap (half_pos hsigma))
  refine ⟨ηstar, hηstar, hηcap'.trans (min_le_left _ _),
    εstar, hεstar, hεcap'.trans (min_le_left _ _), ?_⟩
  intro rho S D H yStar mStar a b qStar e epsilon eta δgap
    hrho hrhoL hepsilon heps heta h p hp hgap hbar
  have hsmall : epsilon + eta ≤ sigma := by
    have h1 := heps.trans (hεcap'.trans (min_le_right _ _))
    have h2 := heta.trans (hηcap'.trans (min_le_right _ _))
    linarith only [h1, h2]
  have hpoint := (hcomparison rho S D H yStar mStar a b qStar e epsilon eta
    hrho hrhoL hepsilon h hsmall).2 p hp
  have hmass : |S.m p.1 p.2 - mStar (S.r p.1 p.2)| ≤ C * (epsilon + eta) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hpoint
  exact hcontradict δgap (S.r p.1 p.2) (S.m p.1 p.2) (mStar (S.r p.1 p.2))
    epsilon eta heps heta (hrho.trans hp.2.1) (h.box p hp).2.2.1.1
    (by simpa only [Fields.mu] using hgap) hmass hbar

end EmcsfAcExtension.Global.Observation
