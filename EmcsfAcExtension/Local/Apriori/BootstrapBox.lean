module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.BootstrapParameters
import EmcsfAcExtension.Local.Apriori.BootstrapTopology
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Discharging the bootstrap with a positive scalar margin

The bootstrap runs with `ε > datumVar h T`, as required by definitions-audit
note N3. Its continuous scalar barrier is maximized only over complete
triangles, and the vertex uses the original initial scalar value.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

private noncomputable def bootstrapExcess (S : Fields) (ε M : ℝ) (p : ℝ × ℝ) : ℝ :=
  max (|S.lam p.1 p.2 - 1 / 2| - 1 / 4)
    (max (|-S.nu p.1 p.2 - 1 / 2| - 1 / 4)
      (max (S.mu p.1 p.2 - 1 / 2) (max (‖S.phi p.1 p.2‖ - M)
        (max (‖S.theta p.1 p.2 / S.lam p.1 p.2‖ - 4 * ε)
          (‖S.xi p.1 p.2 / S.nu p.1 p.2‖ - 4 * ε)))))

/-- Classical restart data have finite actual variation. This assertion
uses the initial normalized scalar trace and no bootstrap bound or
uniform control of higher derivatives. -/
theorem datum_variation_ne_top_of_classical_data {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) (hdata : IsRestartData S h T) :
    eVariationOn h (Icc 0 T) ≠ ⊤ := by
  have ca : ContDiffOn ℝ 1 (S.a 0) (Icc 0 T) :=
    hS.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have ch : ContDiffOn ℝ 1 h (Icc 0 T) :=
    ca.congr (fun v hv => (hdata.1 v hv).2.symm)
  have hac : AbsolutelyContinuousOnInterval h 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT.le] using ch
  exact hac.boundedVariationOn_Icc hT.le

private theorem excess_continuous {e T ε M : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (bootstrapExcess S ε M) (triangle 0 T) := by
  have cl := hS.c1_lam.continuousOn
  have cn := hS.c1_nu.continuousOn
  have cm := continuousOn_mu_aux hT hS
  have cy := hS.c1_theta.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')
  have cz := hS.c1_xi.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)
  exact ((cl.sub continuousOn_const).abs.sub continuousOn_const).sup
    (((cn.neg.sub continuousOn_const).abs.sub continuousOn_const).sup
      ((cm.sub continuousOn_const).sup ((hS.c1_phi.continuousOn.norm.sub continuousOn_const).sup
        ((cy.norm.sub continuousOn_const).sup (cz.norm.sub continuousOn_const)))))

private theorem box_of_excess_nonpos {S : Fields} {ε M s : ℝ}
    (hF : ∀ p ∈ triangle 0 s, bootstrapExcess S ε M p ≤ 0) :
    BootBox S ε M (triangle 0 s) := by
  intro p hp
  have hi := hF p hp
  simp only [bootstrapExcess, max_le_iff, sub_nonpos] at hi
  rcases hi with ⟨hl, hn, hm, hφ, hθ, hξ⟩
  have hl' := abs_le.mp hl
  have hn' := abs_le.mp hn
  refine ⟨?_, ?_, ?_, ?_, ?_, hφ, hθ, hξ⟩ <;>
    linarith only [hl'.1, hl'.2, hn'.1, hn'.2, hm]

private theorem initial_expansion {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) (hdata : IsRestartData S h T) :
    S.lam 0 0 = 1 / 2 := by
  have hs : MapsTo (fun x : ℝ => (0, x)) (Icc 0 T) (triangle 0 T) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hd := hasDerivWithinAt_pdV hS.c1_r (hs ⟨le_rfl, hT.le⟩) hs
  rw [(radius_axis_partials_aux hT hS ⟨le_rfl, hT.le⟩).2] at hd
  have hg : HasDerivWithinAt (S.r 0) (1 / 2) (Icc 0 T) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 2).hasDerivWithinAt.congr_of_mem
      (fun x hx => (hdata.1 x hx).1) ⟨le_rfl, hT.le⟩
  exact (hd.derivWithin (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩)).symm.trans
    (hg.derivWithin (uniqueDiffOn_Icc hT 0 ⟨le_rfl, hT.le⟩))

private theorem excess_vertex_negative {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) (hdata : IsRestartData S h T)
    (hε : 0 < ε) (hM : M = 1 + ‖h 0‖ + 10 * ε) : bootstrapExcess S ε M (0, 0) < 0 := by
  have ha := hS.axis 0 ⟨le_rfl, le_rfl, hT.le⟩
  have hl := initial_expansion hT hS hdata
  have hn : S.nu 0 0 = -(1 / 2) := by linarith only [ha.2.2.2.1, hl]
  have hm : S.mu 0 0 = 0 := by simp [Fields.mu, ha.1]
  have hθ : S.theta 0 0 / S.lam 0 0 = 0 := by
    have h := ha.2.2.2.2.1
    change S.phi 0 0 + S.theta 0 0 / S.lam 0 0 = S.phi 0 0 at h
    exact add_eq_left.mp h
  have hξ : S.xi 0 0 / S.nu 0 0 = 0 := by
    have h := ha.2.2.2.2.2
    change S.phi 0 0 + S.xi 0 0 / S.nu 0 0 = S.phi 0 0 at h
    exact add_eq_left.mp h
  have hφ : S.phi 0 0 = h 0 := ha.2.2.2.2.1.symm.trans (hdata.1 0 ⟨le_rfl, hT.le⟩).2
  dsimp only [bootstrapExcess]
  rw [hθ, hξ, hφ, hl, hn, hm]
  simp only [norm_zero, max_lt_iff]
  rw [hM]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith only [hε]

/-- Every sufficiently small classical restart solution satisfies the
complete bootstrap box when the control parameter has a positive excess
over the actual datum variation. Universal thresholds are chosen before
all data; no temporary box or higher derivative bound is a premise. This
is the N3 positive-margin discharge used before passing to `SmoothBounds`. -/
theorem bootBox_of_positive_margin : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    0 < T → IsC1Solution e S (triangle 0 T) → IsRestartData S h T →
    datumVar h T < ε → M = 1 + ‖h 0‖ + 10 * ε →
    ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ → BootBox S ε M (triangle 0 T) := by
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hparameter⟩ := bootstrap_parameter_choice
  refine ⟨ε₀, δ₀, hε₀, hδ₀, ?_⟩
  intro e T ε M S h hT hS hdata hεdata hM hε hδ
  have hεp : 0 < ε := lt_of_le_of_lt ENNReal.toReal_nonneg hεdata
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hfinite := datum_variation_ne_top_of_classical_data hT hS hdata
  have hneg := complete_triangle_barrier hT (excess_continuous hT hS)
    (excess_vertex_negative hT hS hdata hεp hM) (by
      intro s hs hclosed p hp
      rcases eq_or_lt_of_le hs.1 with hs0 | hs0
      · change 0 = s at hs0
        subst s
        have hp0 : p = (0, 0) := by
          apply Prod.ext <;> linarith only [hp.1, hp.2.1, hp.2.2]
        rw [hp0]
        exact excess_vertex_negative hT hS hdata hεp hM
      · have hsub := triangle_subset_triangle hs.2
        have hset : AprioriSetting e s ε M S h :=
          ⟨hs0, hS.mono hsub (uniqueDiffOn_triangle hs0), isRestartData_mono hdata hs.2,
            (ENNReal.toReal_mono hfinite
              (eVariationOn.mono h (Icc_subset_Icc le_rfl hs.2))).trans hεdata.le,
            hM, box_of_excess_nonpos hclosed⟩
        have hd : |e| * (s / 2) * M ≤ δ₀ := by
          apply le_trans (b := |e| * (T / 2) * M) ?_ hδ
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs.2 (by norm_num))
              (abs_nonneg e)) hM0
        obtain ⟨hl0, hl1, hn0, hn1, hm, hθ, hξ, _, hφ⟩ :=
          hparameter e s ε M S h hset hε hd p.1 p.2 hp
        have hl : |S.lam p.1 p.2 - 1 / 2| < 1 / 4 := by
          apply abs_lt.mpr
          constructor <;> linarith only [hl0, hl1]
        have hn : |-S.nu p.1 p.2 - 1 / 2| < 1 / 4 := by
          apply abs_lt.mpr
          constructor <;> linarith only [hn0, hn1]
        simp only [bootstrapExcess, max_lt_iff, sub_neg]
        refine ⟨hl, hn, ?_, hφ, ?_, ?_⟩ <;> linarith only [hm, hθ, hξ, hεp])
  exact box_of_excess_nonpos (fun p hp => (hneg p hp).le)

end EmcsfAcExtension.Local
