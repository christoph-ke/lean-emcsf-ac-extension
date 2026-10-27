module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.PositiveExpIntegrand
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Terminal.Correction
import EmcsfAcExtension.Local.Calculus.RelativeCharge

/-! # Uniform positive exponents on compact sets meeting the regular axis

The internal project record estimate uses the complete outgoing hull of each incoming section.
Outgoing mass monotonicity gives nonnegative mass, and relative charge gives
the fourth-power radius bound for charge. The logarithmic radius equation
then bounds proper positive integrals uniformly. Monotone convergence is
applied in the extended nonnegative reals before any finiteness assertion.
Source: `charged_SF_new_version.tex:L4199`–L4215; internal project record.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

variable {e : ℝ} {S : Fields} {D K : Set (ℝ × ℝ)}

/-- Nonnegativity of the mass ratio follows from the outgoing mass equation
and its zero regular-axis trace on the full outgoing hull. No sign hypothesis
on the mass is needed. -/
theorem mu_nonneg_of_outgoing_hull (hS : IsSolution e S D) {u v : ℝ}
    (huv : u ≤ v) (hs : outSeg u u v ⊆ D) : 0 ≤ S.mu u v := by
  have ha := hS.axis u (hs ⟨rfl, le_rfl, huv⟩)
  have hm := Gap.mass_out_le hS le_rfl huv hs
  rw [ha.2.1] at hm
  rcases huv.eq_or_lt with rfl | huv
  · simp [Fields.mu, ha.1]
  · exact div_nonneg (mul_nonneg (by norm_num) hm)
      (hS.r_pos (u, v) (hs ⟨rfl, huv.le, le_rfl⟩) huv).le

/-- The compact-axis charge estimate has the exact coefficient
`e² M² / (3δ)`, uniform in the point, solution, and domain once the scalar
bound `M` and positive gap `δ` hold on the full outgoing cone. -/
theorem charge_sq_le_radius_four (hS : IsSolution e S D) {u v δ M : ℝ}
    (huv : u < v) (hs : outSeg u u v ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hphi : ∀ s ∈ Icc u v, ‖S.phi u s‖ ≤ M) :
    S.Q u v ^ 2 ≤ (e ^ 2 * M ^ 2 / (3 * δ)) * S.r u v ^ 4 := by
  have hp := hs (show (u, v) ∈ outSeg u u v from ⟨rfl, huv.le, le_rfl⟩)
  have hr := hS.r_pos (u, v) hp huv
  have hμ : S.mu u v ≤ 1 := by linarith only [hS.one_sub_mu_pos (u, v) hp]
  have hc : 0 ≤ e ^ 2 * M ^ 2 * S.r u v ^ 2 / (3 * δ) := by positivity
  have hq := (Local.eq_relative_charge hS huv hs hδ hgap hphi).trans
    (mul_le_of_le_one_right hc hμ)
  have hq' := (div_le_iff₀ (sq_pos_of_pos hr)).mp hq
  calc
    _ ≤ _ := hq'
    _ = _ := by ring

private theorem correction_le (hS : IsSolution e S D) {u v δ M : ℝ}
    (huv : u < v) (hs : outSeg u u v ⊆ D) (hδ : 0 < δ) (hM : 0 < M)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hphi : ∀ s ∈ Icc u v, ‖S.phi u s‖ ≤ M)
    (hn : -S.nu u v ≤ M) (hrM : S.r u v ≤ M) :
    -S.nu u v * S.Q u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 3) ≤
      (e ^ 2 * M ^ 2 / (3 * δ)) * M ^ 2 / δ := by
  have hp := hs (show (u, v) ∈ outSeg u u v from ⟨rfl, huv.le, le_rfl⟩)
  have hr := hS.r_pos (u, v) hp huv
  have hg := hS.one_sub_mu_pos (u, v) hp
  let c := e ^ 2 * M ^ 2 / (3 * δ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq : S.Q u v ^ 2 / S.r u v ^ 4 ≤ c :=
    (div_le_iff₀ (pow_pos hr 4)).mpr
      (charge_sq_le_radius_four hS huv hs hδ hgap hphi)
  have hnr : -S.nu u v * S.r u v ≤ M ^ 2 := by
    calc
      _ ≤ M * M := mul_le_mul hn hrM hr.le hM.le
      _ = _ := (pow_two M).symm
  calc
    _ = ((-S.nu u v * S.r u v) * (S.Q u v ^ 2 / S.r u v ^ 4)) /
        (1 - S.mu u v) := by field_simp [hr.ne', hg.ne']
    _ ≤ (M ^ 2 * c) / (1 - S.mu u v) :=
      div_le_div_of_nonneg_right
        (mul_le_mul hnr hq (div_nonneg (sq_nonneg _) (pow_nonneg hr.le 4))
          (sq_nonneg M)) hg.le
    _ ≤ (M ^ 2 * c) / δ :=
      div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg M) hc) hδ
        (hgap v ⟨huv.le, le_rfl⟩)
    _ = _ := by dsimp [c]; ring

/-- An explicit bound for every incoming section whose outgoing hull lies
in `K`. The parameters `ℓ,δ,M` bound the expansion, gap, scalar, radius,
incoming expansion, and first coordinate on `K`. The displayed coefficient
depends only on `e,ℓ,δ,M`, uniformly in the section and its endpoints.
The last endpoint may be on the regular axis. -/
theorem incoming_positive_exponent_le_of_compact_bounds
    (hS : IsSolution e S D) (hKD : K ⊆ D)
    (hhull : ∀ p ∈ K, outSeg p.1 p.1 p.2 ⊆ K)
    {ℓ δ M : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hM : 0 < M)
    (hbounds : ∀ p ∈ K, ℓ ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ M ∧
      -S.nu p.1 p.2 ≤ M ∧ S.r p.1 p.2 ≤ M ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
      |p.1| ≤ M ∧ δ ≤ 1 - S.mu p.1 p.2)
    {a b v : ℝ} (hab : a ≤ b) (hbv : b ≤ v) (hs : inSeg a b v ⊆ K) :
    (∫⁻ u in Ico a b, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
      ENNReal.ofReal (|Real.log M - Real.log ℓ| +
        (e ^ 2 * M ^ 2 / (3 * δ)) * M ^ 2 / δ * (2 * M)) := by
  let c := (e ^ 2 * M ^ 2 / (3 * δ)) * M ^ 2 / δ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have mem (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ K := hs ⟨hu.1, hu.2, rfl⟩
  have hpos (u : ℝ) (hu : u ∈ Ico a b) : 0 ≤ positiveExpIntegrand S u v :=
    Terminal.positive_integrand_nonneg hS (hKD (mem u ⟨hu.1, hu.2.le⟩))
      (hu.2.trans_le hbv)
      (mu_nonneg_of_outgoing_hull hS (hu.2.trans_le hbv).le
        ((hhull _ (mem u ⟨hu.1, hu.2.le⟩)).trans hKD))
  have htrunc (w : ℝ) (haw : a ≤ w) (hwb : w < b) :
      (∫ u in a..w, positiveExpIntegrand S u v) ≤
        |Real.log M - Real.log ℓ| + c * (2 * M) := by
    have hwv := hwb.trans_le hbv
    have hsw : inSeg a w v ⊆ D :=
      ((inSeg_subset_inSeg le_rfl hwb.le).trans hs).trans hKD
    have hcont := Terminal.incoming_integrands_continuousOn hS hwv hsw
    have hi := hcont.1.intervalIntegrable_of_Icc (μ := volume) haw
    have hcorr := hcont.2.2.intervalIntegrable_of_Icc (μ := volume) haw
    have he : (∫ u in a..w, positiveExpIntegrand S u v) =
        (∫ u in a..w, signedExpIntegrand S u v) +
          ∫ u in a..w, -S.nu u v * S.Q u v ^ 2 /
            ((1 - S.mu u v) * S.r u v ^ 3) := by
      rw [← intervalIntegral.integral_add hi hcorr]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc a w := by simpa only [uIcc_of_le haw] using hu
      have hp : (u, v) ∈ D := hsw ⟨hu'.1, hu'.2, rfl⟩
      exact Terminal.positive_eq_signed_add_correction
        (hS.r_pos (u, v) hp (hu'.2.trans_lt hwv)).ne'
        (hS.one_sub_mu_pos (u, v) hp).ne'
    have hlog := (Terminal.incoming_log_lambda_integralForm hS haw hwv hsw).2
    rw [intervalIntegral.integral_neg] at hlog
    have haK := mem a ⟨le_rfl, haw.trans hwb.le⟩
    have hwK := mem w ⟨haw, hwb.le⟩
    have hlogbound : (∫ u in a..w, signedExpIntegrand S u v) ≤
        |Real.log M - Real.log ℓ| := by
      have hu := Real.log_le_log (hS.lam_pos (a, v) (hKD haK)) (hbounds _ haK).2.1
      have hl := Real.log_le_log hℓ (hbounds _ hwK).1
      have ha := le_abs_self (Real.log M - Real.log ℓ)
      linarith only [hlog, hu, hl, ha]
    have hcorrbound : (∫ u in a..w, -S.nu u v * S.Q u v ^ 2 /
        ((1 - S.mu u v) * S.r u v ^ 3)) ≤ c * (w - a) := by
      calc
        _ ≤ ∫ _u in a..w, c := by
          apply intervalIntegral.integral_mono_on haw hcorr intervalIntegrable_const
          intro u hu
          have huK := mem u ⟨hu.1, hu.2.trans hwb.le⟩
          have hh := hhull _ huK
          apply correction_le hS (hu.2.trans_lt hwv) (hh.trans hKD) hδ hM
          · intro s hsu
            have hsK : (u, s) ∈ K := hh ⟨rfl, hsu.1, hsu.2⟩
            exact (hbounds _ hsK).2.2.2.2.2.2
          · intro s hsu
            have hsK : (u, s) ∈ K := hh ⟨rfl, hsu.1, hsu.2⟩
            exact (hbounds _ hsK).2.2.2.2.1
          · exact (hbounds _ huK).2.2.1
          · exact (hbounds _ huK).2.2.2.1
        _ = _ := by simp [mul_comm]
    have hlength : w - a ≤ 2 * M := by
      have ha := (abs_le.mp (hbounds _ haK).2.2.2.2.2.1).1
      have hw := (abs_le.mp (hbounds _ hwK).2.2.2.2.2.1).2
      linarith only [ha, hw]
    rw [he]
    exact add_le_add hlogbound (hcorrbound.trans (mul_le_mul_of_nonneg_left hlength hc))
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨w, hwmono, hw, hwlim⟩ := exists_seq_strictMono_tendsto' hab
  rw [lintegral_ofReal_Ico_eq_iSup_intervalIntegral hwmono.monotone
    (fun n => (hw n).2.le) hwlim (fun n => (hw n).1.le)]
  · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal
      (htrunc (w n) (hw n).1.le (hw n).2))
  · intro n
    have hn := Terminal.incoming_integrands_continuousOn hS ((hw n).2.trans_le hbv)
      (((inSeg_subset_inSeg le_rfl (hw n).2.le).trans hs).trans hKD)
    exact hn.2.1.intervalIntegrable_of_Icc (hw n).1.le
  · exact hpos

/-- A compact set closed under complete outgoing hulls has one finite positive
incoming exponent bound, including sections ending on its regular axis.
The constant may depend on fixed `e,S,D,K`, uniformly in all three section labels.
The positive gap minimum uses the frozen two-dimensional `axis_mu` limit. -/
theorem compact_axis_positive_exponent_bound (hS : IsSolution e S D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hhull : ∀ p ∈ K, outSeg p.1 p.1 p.2 ⊆ K) :
    ∃ C > 0, ∀ a b v : ℝ, a ≤ b → b ≤ v → inSeg a b v ⊆ K →
      (∫⁻ u in Ico a b, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C := by
  obtain ⟨ℓ, hℓ, hlo⟩ := hK.exists_forall_le' (hS.cont_lam.mono hKD)
    (fun p hp => hS.lam_pos p (hKD hp))
  obtain ⟨δ, hδ, hgap⟩ := hK.exists_forall_le'
    (continuousOn_const.sub ((Gap.continuousOn_mu hS).mono hKD))
    (fun p hp => hS.one_sub_mu_pos p (hKD hp))
  let F : ℝ × ℝ → ℝ := fun p => |S.lam p.1 p.2| + |S.nu p.1 p.2| +
    |S.r p.1 p.2| + ‖S.phi p.1 p.2‖ + |p.1|
  have hF : ContinuousOn F K :=
    ((((hS.cont_lam.mono hKD).abs.add (hS.cont_nu.mono hKD).abs).add
      (hS.cont_r.mono hKD).abs).add (hS.cont_phi.mono hKD).norm).add
        continuous_fst.abs.continuousOn
  obtain ⟨U, hU⟩ := hK.bddAbove_image hF
  let M := |U| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ p ∈ K, ℓ ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ M ∧
      -S.nu p.1 p.2 ≤ M ∧ S.r p.1 p.2 ≤ M ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
      |p.1| ≤ M ∧ δ ≤ 1 - S.mu p.1 p.2 := by
    intro p hp
    have hu : F p ≤ U := hU (mem_image_of_mem F hp)
    dsimp [F] at hu
    have hUM : U ≤ M := (le_abs_self U).trans (le_add_of_nonneg_right zero_le_one)
    have hsum := hu.trans hUM
    have hl := le_abs_self (S.lam p.1 p.2)
    have hn := neg_le_abs (S.nu p.1 p.2)
    have hr := le_abs_self (S.r p.1 p.2)
    have n1 := abs_nonneg (S.lam p.1 p.2)
    have n2 := abs_nonneg (S.nu p.1 p.2)
    have n3 := abs_nonneg (S.r p.1 p.2)
    have n4 := norm_nonneg (S.phi p.1 p.2)
    have n5 := abs_nonneg p.1
    exact ⟨hlo p hp, by linarith only [hsum, hl, n2, n3, n4, n5],
      by linarith only [hsum, hn, n1, n3, n4, n5],
      by linarith only [hsum, hr, n1, n2, n4, n5],
      by linarith only [hsum, n1, n2, n3, n5],
      by linarith only [hsum, n1, n2, n3, n4], hgap p hp⟩
  let C := |Real.log M - Real.log ℓ| +
    (e ^ 2 * M ^ 2 / (3 * δ)) * M ^ 2 / δ * (2 * M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  intro a b v hab hbv hs
  exact (incoming_positive_exponent_le_of_compact_bounds hS hKD hhull
    hℓ hδ hM hb hab hbv hs).trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))

end EmcsfAcExtension.Global.Closure
