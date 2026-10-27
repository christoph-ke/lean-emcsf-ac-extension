module

public import EmcsfAcExtension.Global.Observation.Static.OuterFromInverse
public import EmcsfAcExtension.Global.Observation.Static.InnerReference
import Mathlib

/-! # Matched outer and stopped inner radial references

Each inner reference continues the same compact-family member used by
the outer comparison. Only its own selected stopping interval is used.
Source: charged_SF_new_version.tex:L2196–2239, L2731–2780; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Construct matched radial references with a common strict barrier after
the fixed outer comparison cutoff. All radii, margins and coefficient
bounds depend only on `δ,Lmin`, before every normalized member and its
outer radius. The outer scalar coefficient is the universal number 41.
The two references have identical mass and scalar ratio at `Lzero` and
are compared only down to their own selected positive stopping radius. -/
theorem uniform_radial_references (δ Lmin : ℝ) (hδ : δ ∈ Ioo 0 1) :
    ∃ Lzero rStar γ C : ℝ,
      0 < Lzero ∧ Lmin ≤ Lzero ∧ 128 ≤ Lzero ∧
      0 < rStar ∧ rStar ≤ Lzero ∧ 0 < γ ∧ 0 < C ∧
    ∀ L M q : ℝ, ∀ P : ℂ, Lzero ≤ L → 0 ≤ M → M + ‖P‖ + |q| = 1 →
    ∃ rho ∈ Icc rStar Lzero,
    ∃ (phiOut yOut : ℝ → ℂ) (mOut : ℝ → ℝ) (yIn : ℝ → ℂ) (mIn : ℝ → ℝ),
      (AbsolutelyContinuousOnInterval mOut Lzero L ∧
        ContinuousOn phiOut (Icc Lzero L) ∧ ContinuousOn yOut (Icc Lzero L) ∧
        mOut L = M ∧ phiOut L = P / (L : ℂ) ∧ phiOut L + yOut L = 0 ∧
        (∀ r ∈ Icc Lzero L,
          let k := (2 * mOut r / r - q ^ 2 / r ^ 2) / (1 - 2 * mOut r / r)
          HasDerivAt (fun x : ℝ => (x : ℂ) * phiOut x) (phiOut r + yOut r) r ∧
          HasDerivAt (fun x => phiOut x + yOut x) ((-k / r : ℝ) * yOut r) r ∧
          HasDerivAt mOut ((1 - 2 * mOut r / r) * ‖yOut r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r) ∧
        ∀ r ∈ Icc Lzero L,
          |mOut r| ≤ 2 ∧ ‖yOut r‖ ≤ 41 / r ∧ |1 - 2 * mOut r / r| ≤ 2 ∧
          ‖(r : ℂ) * phiOut r‖ ≤ 41 ∧ ‖phiOut r + yOut r‖ ≤ 41 / r ^ 2 ∧
          1 / 2 ≤ 1 - 2 * mOut r / r) ∧
      (ContinuousOn yIn (Icc rho Lzero) ∧ ContinuousOn mIn (Icc rho Lzero) ∧
        (∀ r ∈ Icc rho Lzero, ‖yIn r‖ ≤ C ∧
          1 / (C + 1) ≤ 1 - 2 * mIn r / r ∧ |1 - 2 * mIn r / r| ≤ 1 + 2 * C ^ 2) ∧
        ∀ r ∈ Ioo rho Lzero,
          let k := (2 * mIn r / r - q ^ 2 / r ^ 2) / (1 - 2 * mIn r / r)
          HasDerivAt yIn (((-(1 + k) / r : ℝ) : ℂ) * yIn r) r ∧
          HasDerivAt mIn ((1 - 2 * mIn r / r) * ‖yIn r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r) ∧
      yIn Lzero = yOut Lzero ∧ mIn Lzero = mOut Lzero ∧
      (mIn rho ≤ -γ ∨ 1 - 2 * mIn rho / rho ≤ δ - γ) := by
  obtain ⟨a, width, r, γ, C, ha, hw, haw, ha128, hcut, hr, hγ, hC,
      outer, hout, hinner⟩ := uniform_static_barriers_after_cutoff δ (max Lmin 128) hδ
  let Lzero := a⁻¹
  let rStar := min r Lzero
  have hLzero : 0 < Lzero := inv_pos.mpr ha
  have hcutMin : Lmin ≤ Lzero := (le_max_left _ _).trans hcut
  have hcut128 : 128 ≤ Lzero := (le_max_right _ _).trans hcut
  refine ⟨Lzero, rStar, γ, C, hLzero, hcutMin, hcut128, lt_min hr hLzero,
    min_le_right _ _, hγ, hC, ?_⟩
  intro L M q P hL hM hnorm
  have hLp : 0 < L := hLzero.trans_le hL
  have hxLa : L⁻¹ ≤ a := by
    simpa only [one_div, inv_inv, Lzero] using one_div_le_one_div_of_le hLzero hL
  let p : ℝ × ℂ × ℝ × ℝ := (M, P, q, L⁻¹)
  have hp : 0 ≤ p.1 ∧ p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a :=
    ⟨hM, hnorm, (inv_pos.mpr hLp).le, hxLa⟩
  let zOut := outer p
  obtain ⟨rho, hrho, zIn, hzIn0, hzIn, hboxIn, hbarrier⟩ := hinner p hp
  have hrhop : 0 < rho := hr.trans_le hrho.1
  have hRho : rho ∈ Icc rStar Lzero := ⟨(min_le_left _ _).trans hrho.1, hrho.2⟩
  have hPbound : ‖P‖ ≤ 1 := by linarith only [hM, hnorm, abs_nonneg q]
  have hqbound : |q| ≤ 1 := by linarith only [hM, hnorm, norm_nonneg P]
  have hextended : Icc L⁻¹ a ⊆ Icc (L⁻¹ - 2 * width) (L⁻¹ + 2 * width) :=
    Icc_subset_Icc (by linarith only [hw])
      (by linarith only [(inv_pos.mpr hLp).le, haw, hw])
  have hinit : zOut L⁻¹ = (M, 1 / 2, P * (L⁻¹ : ℝ)) := (hout p hp).1
  have hd (x) (hx : x ∈ Icc L⁻¹ a) :
      HasDerivAt zOut (staticInvRadiusRHS P q x (zOut x)) x := by
    have hh := (hout p hp).2.1 x (hextended hx)
    apply hh.hasDerivAt
    exact Icc_mem_nhds (by linarith only [hx.1, hw])
      (by linarith only [hx.2, haw, hw, (inv_pos.mpr hLp).le])
  have hbox (x) (hx : x ∈ Icc L⁻¹ a) :
      |x| ≤ 1 / 32 ∧ |(zOut x).1| ≤ 2 ∧ (zOut x).2.1 ∈ Icc (1 / 4) 1 := by
    have hh := (hout p hp).2.2 x (hextended hx)
    exact ⟨hh.1, hh.2.1, hh.2.2.1⟩
  have hscalar := static_outer_scalar_bounds_of_solution P q M L⁻¹ a zOut
    hPbound hqbound (inv_pos.mpr hLp).le hxLa hinit hd hbox
  have hraw (x) (hx : x ∈ Icc L⁻¹ Lzero⁻¹) :
      HasDerivAt zOut (staticInvRadiusRHS P q x (zOut x)) x ∧
      (zOut x).2.1 ∈ Icc (1 / 4) 1 ∧ |(zOut x).1| ≤ 2 ∧
      1 / 2 ≤ 1 - 2 * x * (zOut x).1 ∧
      ‖(zOut x).2.2‖ + ‖(P / ((2 * (zOut x).2.1 : ℝ) : ℂ)) * x‖ ≤ 40 * x ∧
      ‖(zOut x).2.2 - (P / ((2 * (zOut x).2.1 : ℝ) : ℂ)) * x‖ ≤ 40 * x ^ 2 := by
    have hx' : x ∈ Icc L⁻¹ a := by simpa only [Lzero, inv_inv] using hx
    have hb := hbox x hx'
    have hs := hscalar x hx'
    have hprod : |2 * x * (zOut x).1| ≤ 1 / 8 := by
      calc
        |2 * x * (zOut x).1| = 2 * |x| * |(zOut x).1| := by rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * (1 / 32) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hb.1 (by norm_num)) hb.2.1
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    refine ⟨hd x hx', hb.2.2, hb.2.1, ?_, ?_, hs.2⟩
    · linarith only [le_abs_self (2 * x * (zOut x).1), hprod]
    · have hx0 : 0 ≤ x := (inv_pos.mpr hLp).le.trans hx'.1
      linarith only [hs.1, hx0]
  obtain ⟨phiOut, yOut, mOut, hmId, _hphiId, hyId, houter⟩ :=
    outer_radial_reference_of_inverse_solution hcut128 hL (by norm_num : (0 : ℝ) < 40)
      zOut hinit hraw
  have h41 : (40 : ℝ) + 1 = 41 := by norm_num
  rw [h41] at houter
  let mIn := fun x : ℝ => (zIn x⁻¹).1
  let yIn := fun x : ℝ => -P / ((2 * x * (zIn x⁻¹).2.1 : ℝ) : ℂ)
  have hin := inner_radial_reference_of_stopped_solution ha hrhop hrho.2 hC zIn hzIn hboxIn
  have hmatchY : yIn Lzero = yOut Lzero := by
    rw [hyId]
    change -P / ((2 * a⁻¹ * (zIn (a⁻¹)⁻¹).2.1 : ℝ) : ℂ) =
      -P / ((2 * a⁻¹ * (outer p (a⁻¹)⁻¹).2.1 : ℝ) : ℂ)
    rw [inv_inv, hzIn0]
  have hmatchM : mIn Lzero = mOut Lzero := by
    rw [hmId]
    change (zIn (a⁻¹)⁻¹).1 = (outer p (a⁻¹)⁻¹).1
    rw [inv_inv, hzIn0]
  refine ⟨rho, hRho, phiOut, yOut, mOut, yIn, mIn, houter, hin, hmatchY, hmatchM, ?_⟩
  rcases hbarrier with hm | hg
  · exact Or.inl hm
  · right
    change 1 - 2 * (zIn rho⁻¹).1 / rho ≤ δ - γ
    convert hg using 1
    ring

end EmcsfAcExtension.Global.Observation
