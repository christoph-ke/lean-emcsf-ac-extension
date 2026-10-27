module

public import EmcsfAcExtension.Global.Conclusion.CompactAxis
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Terminal.Correction
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The exact compact-axis graph contract

This refines the landed finite compact bound to the five-extrema coefficient
of approved internal project record:L58–113. The radius-square FTC retains the factor 1/6.
No shrinking construction, continuation or local-existence input is needed.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

private theorem correction_le_radius_weight {e u v δ Φ : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (huv : u < v)
    (hs : outSeg u u v ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hphi : ∀ s ∈ Icc u v, ‖S.phi u s‖ ≤ Φ) :
    -S.nu u v * S.Q u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 3) ≤
      (e ^ 2 * Φ ^ 2 / (3 * δ ^ 2)) * (-S.nu u v * S.r u v) := by
  have hp := hs (show (u, v) ∈ outSeg u u v from ⟨rfl, huv.le, le_rfl⟩)
  have hr := hS.r_pos (u, v) hp huv
  have hg := hS.one_sub_mu_pos (u, v) hp
  have hn := neg_pos.mpr (hS.nu_neg (u, v) hp)
  let c := e ^ 2 * Φ ^ 2 / (3 * δ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq : S.Q u v ^ 2 / S.r u v ^ 4 ≤ c :=
    (div_le_iff₀ (pow_pos hr 4)).mpr
      (charge_sq_le_radius_four hS huv hs hδ hgap hphi)
  calc
    _ = ((-S.nu u v * S.r u v) * (S.Q u v ^ 2 / S.r u v ^ 4)) /
        (1 - S.mu u v) := by field_simp [hr.ne', hg.ne']
    _ ≤ ((-S.nu u v * S.r u v) * c) / (1 - S.mu u v) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (mul_nonneg hn.le hr.le)) hg.le
    _ ≤ ((-S.nu u v * S.r u v) * c) / δ :=
      div_le_div_of_nonneg_left (by positivity) hδ (hgap v ⟨huv.le, le_rfl⟩)
    _ = _ := by dsimp [c]; field_simp

private theorem radius_weight_integral_le {e a w v R : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (haw : a ≤ w) (hwv : w < v)
    (hs : inSeg a w v ⊆ D) (hR : S.r a v ≤ R) :
    (∫ u in a..w, -S.nu u v * S.r u v) ≤ R ^ 2 / 2 := by
  have hr := (Local.IsSolution.in_section hS haw hwv hs).1
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cr : ContinuousOn (fun u => S.r u v) (Icc a w) := by
    simpa only [uIcc_of_le haw] using hr.1.continuousOn
  have hi : IntervalIntegrable (fun u => S.r u v * S.nu u v) volume a w :=
    (cr.mul cn).intervalIntegrable_of_Icc haw
  have hd : ∀ᵐ u, u ∈ uIcc a w →
      HasDerivAt (fun x => S.r x v * S.r x v)
        (S.r u v * S.nu u v + S.r u v * S.nu u v) u := by
    rw [← ae_restrict_iff' measurableSet_uIcc, uIcc_of_le haw]
    exact hr.2.mono fun u hu => by simpa only [Pi.mul_apply, mul_comm] using! hu.mul hu
  have he := (hr.1.mul hr.1).integral_eq_sub_of_ae_hasDerivAt_normed (hi.add hi) hd
  rw [intervalIntegral.integral_add hi hi] at he
  simp only [Pi.mul_apply] at he
  have hn : (∫ u in a..w, -S.nu u v * S.r u v) =
      -(∫ u in a..w, S.r u v * S.nu u v) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _hu
    ring
  have hra := hS.r_pos (a, v) (hs ⟨le_rfl, haw, rfl⟩) (haw.trans_lt hwv)
  have hsq : S.r a v ^ 2 ≤ R ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hra.le hR
  rw [hn]
  nlinarith only [he, hsq, sq_nonneg (S.r w v)]

private theorem exact_positive_exponent_le {e a b v ℓ Λ Φ R δ : ℝ} {S : Fields}
    {D K : Set (ℝ × ℝ)} (hS : IsSolution e S D) (hKD : K ⊆ D)
    (hhull : ∀ p ∈ K, outSeg p.1 p.1 p.2 ⊆ K)
    (hℓ : 0 < ℓ) (hδ : 0 < δ)
    (hbounds : ∀ p ∈ K, ℓ ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ Λ ∧
      ‖S.phi p.1 p.2‖ ≤ Φ ∧ S.r p.1 p.2 ≤ R ∧ δ ≤ 1 - S.mu p.1 p.2)
    (hab : a ≤ b) (hbv : b ≤ v) (hs : inSeg a b v ⊆ K) :
    (∫⁻ u in Ico a b, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
      ENNReal.ofReal (Real.log (Λ / ℓ) + e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2)) := by
  have mem (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ K := hs ⟨hu.1, hu.2, rfl⟩
  have hpos (u : ℝ) (hu : u ∈ Ico a b) : 0 ≤ positiveExpIntegrand S u v :=
    Terminal.positive_integrand_nonneg hS (hKD (mem u ⟨hu.1, hu.2.le⟩))
      (hu.2.trans_le hbv)
      (mu_nonneg_of_outgoing_hull hS (hu.2.trans_le hbv).le
        ((hhull _ (mem u ⟨hu.1, hu.2.le⟩)).trans hKD))
  have htrunc (w : ℝ) (haw : a ≤ w) (hwb : w < b) :
      (∫ u in a..w, positiveExpIntegrand S u v) ≤
        Real.log (Λ / ℓ) + e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2) := by
    have hwv := hwb.trans_le hbv
    have hsw : inSeg a w v ⊆ D :=
      ((inSeg_subset_inSeg le_rfl hwb.le).trans hs).trans hKD
    have hc := Terminal.incoming_integrands_continuousOn hS hwv hsw
    have hi := hc.1.intervalIntegrable_of_Icc (μ := volume) haw
    have hq := hc.2.2.intervalIntegrable_of_Icc (μ := volume) haw
    have he : (∫ u in a..w, positiveExpIntegrand S u v) =
        (∫ u in a..w, signedExpIntegrand S u v) +
          ∫ u in a..w, -S.nu u v * S.Q u v ^ 2 /
            ((1 - S.mu u v) * S.r u v ^ 3) := by
      rw [← intervalIntegral.integral_add hi hq]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc a w := by simpa only [uIcc_of_le haw] using hu
      have hp : (u, v) ∈ D := hsw ⟨hu'.1, hu'.2, rfl⟩
      exact Terminal.positive_eq_signed_add_correction
        (hS.r_pos (u, v) hp (hu'.2.trans_lt hwv)).ne'
        (hS.one_sub_mu_pos (u, v) hp).ne'
    have haK := mem a ⟨le_rfl, haw.trans hwb.le⟩
    have hwK := mem w ⟨haw, hwb.le⟩
    have hΛ : 0 < Λ := (hS.lam_pos (a, v) (hKD haK)).trans_le (hbounds _ haK).2.1
    have hlog := (Terminal.incoming_log_lambda_integralForm hS haw hwv hsw).2
    rw [intervalIntegral.integral_neg] at hlog
    have hlogbound : (∫ u in a..w, signedExpIntegrand S u v) ≤ Real.log (Λ / ℓ) := by
      rw [Real.log_div hΛ.ne' hℓ.ne']
      have hu := Real.log_le_log (hS.lam_pos (a, v) (hKD haK)) (hbounds _ haK).2.1
      have hl := Real.log_le_log hℓ (hbounds _ hwK).1
      linarith only [hlog, hu, hl]
    let k := e ^ 2 * Φ ^ 2 / (3 * δ ^ 2)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hn := Calculus.continuousOn_in_section hS.cont_nu hsw
    have hr := Calculus.continuousOn_in_section hS.cont_r hsw
    have hni := (hn.neg.mul hr).intervalIntegrable_of_Icc (μ := volume) haw
    have hcorr : (∫ u in a..w, -S.nu u v * S.Q u v ^ 2 /
        ((1 - S.mu u v) * S.r u v ^ 3)) ≤ e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2) := by
      calc
        _ ≤ ∫ u in a..w, k * (-S.nu u v * S.r u v) := by
          apply intervalIntegral.integral_mono_on haw hq (hni.const_mul k)
          intro u hu
          have huK := mem u ⟨hu.1, hu.2.trans hwb.le⟩
          have hh := hhull _ huK
          apply correction_le_radius_weight hS (hu.2.trans_lt hwv) (hh.trans hKD) hδ
          · intro s hsu
            have hsK : (u, s) ∈ K := hh ⟨rfl, hsu.1, hsu.2⟩
            exact (hbounds _ hsK).2.2.2.2
          · intro s hsu
            have hsK : (u, s) ∈ K := hh ⟨rfl, hsu.1, hsu.2⟩
            exact (hbounds _ hsK).2.2.1
        _ = k * (∫ u in a..w, -S.nu u v * S.r u v) :=
          intervalIntegral.integral_const_mul _ _
        _ ≤ k * (R ^ 2 / 2) := mul_le_mul_of_nonneg_left
          (radius_weight_integral_le hS haw hwv hsw (hbounds _ haK).2.2.2.1) hk
        _ = _ := by dsimp [k]; ring
    rw [he]
    exact add_le_add hlogbound hcorr
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨w, hwmono, hw, hwlim⟩ := exists_seq_strictMono_tendsto' hab
  rw [lintegral_ofReal_Ico_eq_iSup_intervalIntegral hwmono.monotone
    (fun n => (hw n).2.le) hwlim (fun n => (hw n).1.le)]
  · exact iSup_le fun n => ENNReal.ofReal_le_ofReal
      (htrunc (w n) (hw n).1.le (hw n).2)
  · intro n
    have hn := Terminal.incoming_integrands_continuousOn hS ((hw n).2.trans_le hbv)
      (((inSeg_subset_inSeg le_rfl (hw n).2.le).trans hs).trans hKD)
    exact hn.2.1.intervalIntegrable_of_Icc (hw n).1.le
  · exact hpos

/-- [node sec:charged-closure#compact-axis-exponent]
The exact internal project record compact-axis contract, approved internal project record:L58–113.
The five constants are attained extrema on `P(c,a,d)`; the displayed bound
depends only on `e,ℓ,Λ,Φ,R,δ`, uniformly in the incoming ray and its cut point.
No smallness or mass-sign hypothesis is added to the frozen solution class. -/
theorem compact_axis_exponent {e c a d : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hca : c ≤ a) (had : a ≤ d)
    (hPD : triangle c d ∩ {p : ℝ × ℝ | p.1 ≤ a} ⊆ D) :
    let P := triangle c d ∩ {p : ℝ × ℝ | p.1 ≤ a}
    (∀ p ∈ P, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) ∧
    ContinuousOn (Function.uncurry S.mu) P ∧
    ∃ ℓ Λ Φ R δ : ℝ, 0 < ℓ ∧ 0 < δ ∧
      IsLeast ((Function.uncurry S.lam) '' P) ℓ ∧
      IsGreatest ((Function.uncurry S.lam) '' P) Λ ∧
      IsGreatest ((fun p => ‖S.phi p.1 p.2‖) '' P) Φ ∧
      IsGreatest ((Function.uncurry S.r) '' P) R ∧
      IsLeast ((fun p => 1 - S.mu p.1 p.2) '' P) δ ∧
      (∀ v ∈ Icc c d, ∀ w ∈ Icc c (min a v),
        (∫⁻ u in Ico c w, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (Real.log (Λ / ℓ) + e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2))) ∧
      (⨆ v ∈ Icc c d, ∫⁻ u in Ico c (min a v),
        ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
          ENNReal.ofReal (Real.log (Λ / ℓ) + e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2)) ∧
      (⨆ v ∈ Icc c d, ∫⁻ u in Ico c (min a v),
        ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤ := by
  let P := triangle c d ∩ {p : ℝ × ℝ | p.1 ≤ a}
  have hP : IsCompact P :=
    (isCompact_triangle c d).inter_right (isClosed_le continuous_fst continuous_const)
  have hne : P.Nonempty := ⟨(c, c), ⟨⟨le_rfl, le_rfl, hca.trans had⟩, hca⟩⟩
  have hhull : ∀ p ∈ P, outSeg p.1 p.1 p.2 ⊆ P := by
    rintro ⟨u, v⟩ ⟨⟨hu, huv, hv⟩, hua⟩ ⟨x, y⟩ ⟨rfl, hy, hyv⟩
    exact ⟨⟨hu, hy, hyv.trans hv⟩, hua⟩
  have cm := (Gap.continuousOn_mu hS).mono hPD
  have cl := hS.cont_lam.mono hPD
  have cp := (hS.cont_phi.mono hPD).norm
  have cr := hS.cont_r.mono hPD
  have cg : ContinuousOn (fun p => 1 - S.mu p.1 p.2) P := continuousOn_const.sub cm
  obtain ⟨pl, hpl, hl⟩ := hP.exists_isMinOn hne cl
  obtain ⟨pL, hpL, hL⟩ := hP.exists_isMaxOn hne cl
  obtain ⟨pp, hpp, hphi⟩ := hP.exists_isMaxOn hne cp
  obtain ⟨pr, hpr, hr⟩ := hP.exists_isMaxOn hne cr
  obtain ⟨pg, hpg, hg⟩ := hP.exists_isMinOn hne cg
  have hℓ := hS.lam_pos pl (hPD hpl)
  have hδ := hS.one_sub_mu_pos pg (hPD hpg)
  refine ⟨?_, cm, ?_⟩
  · intro p hp
    exact ⟨mu_nonneg_of_outgoing_hull hS (hS.subset (hPD hp))
      ((hhull p hp).trans hPD), sub_pos.mp (hS.one_sub_mu_pos p (hPD hp))⟩
  refine ⟨S.lam pl.1 pl.2, S.lam pL.1 pL.2, ‖S.phi pp.1 pp.2‖,
    S.r pr.1 pr.2, 1 - S.mu pg.1 pg.2, hℓ, hδ,
    ⟨mem_image_of_mem _ hpl, by rintro _ ⟨p, hp, rfl⟩; exact hl hp⟩,
    ⟨mem_image_of_mem _ hpL, by rintro _ ⟨p, hp, rfl⟩; exact hL hp⟩,
    ⟨mem_image_of_mem _ hpp, by rintro _ ⟨p, hp, rfl⟩; exact hphi hp⟩,
    ⟨mem_image_of_mem _ hpr, by rintro _ ⟨p, hp, rfl⟩; exact hr hp⟩,
    ⟨mem_image_of_mem _ hpg, by rintro _ ⟨p, hp, rfl⟩; exact hg hp⟩, ?_⟩
  have hbound : ∀ v ∈ Icc c d, ∀ w ∈ Icc c (min a v),
      (∫⁻ u in Ico c w, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal (Real.log (S.lam pL.1 pL.2 / S.lam pl.1 pl.2) +
          e ^ 2 * ‖S.phi pp.1 pp.2‖ ^ 2 * S.r pr.1 pr.2 ^ 2 /
            (6 * (1 - S.mu pg.1 pg.2) ^ 2)) := by
    intro v hv w hw
    apply exact_positive_exponent_le hS hPD hhull hℓ hδ
      (fun p hp' => ⟨hl hp', hL hp', hphi hp', hr hp', hg hp'⟩) hw.1
      (hw.2.trans (min_le_right _ _))
    rintro ⟨u, z⟩ ⟨hu, huw, rfl⟩
    exact ⟨⟨hu, huw.trans (hw.2.trans (min_le_right _ _)), hv.2⟩,
      huw.trans (hw.2.trans (min_le_left _ _))⟩
  have hsup := iSup_le fun v => iSup_le fun hv =>
    hbound v hv (min a v) ⟨le_min hca hv.1, le_rfl⟩
  exact ⟨hbound, hsup, hsup.trans_lt ENNReal.ofReal_lt_top⟩

end EmcsfAcExtension.Global.Closure
