module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregate
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregatePointwise

/-! # The aggregate exterior source estimate

This assembles all six source moments, for the exact charged source.
The coefficient `4096` is numerical and uniform in the coupling, data,
row, inner endpoint and scalar envelope. Source: `charged_SF_new_version.tex:L1298–L1325`,
approved internal project record (S0)–(S4).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Exterior

private theorem numerical_source_sum {a b c d f g : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    4 * (65 * (4 * a) + 326 * (2 * b) + 3 * (32 * c) + 3 * (4 * d) + 2 * f + 2 * g) ≤
      4096 * (a + b + c + d + f + g) := by linarith

/-- [internal]
The aggregate source estimate on one proper exterior row. All derivative
terms occur only through an integral; `SF` bounds the undifferentiated
field `theta/lambda`. The numerical coefficient `4096` is universal.
The terminal consumer discharges every geometric profile hypothesis. -/
theorem charged_exterior_source_bound_of_profiles {ui e u a L SF : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v)
    (hphi : ∀ v ∈ Icc a 0, ‖S.phi u v‖ ≤ L)
    (hQ : ∀ v ∈ Icc a 0, S.Q u v ^ 2 / S.r u v ^ 2 ≤
      64 * (terminalMass S u / S.r u v))
    (hnu : ∀ v ∈ Icc a 0, -S.nu u v ≤ 2 * (-S.nu u 0))
    (hX : terminalMass S u / S.r u a ≤ 1)
    (hF : ∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ SF) :
    (∫ v in a..0, ‖rawDensitySource e S u v‖) ≤
      4096 * (-S.nu u 0) *
        (terminalMass S u / S.r u a ^ 2 *
          (SF + Real.sqrt (terminalMass S u / S.r u a)) +
        |e| * L * (terminalMass S u / S.r u a) *
          Real.sqrt (terminalMass S u / S.r u a) +
        |e| * (terminalMass S u / S.r u a) +
        |e| * L * Real.sqrt (terminalMass S u / S.r u a) +
        e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u)) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cq := (Calculus.continuousOn_out_section h.solution.cont_Q hs).abs
  have cp := (Calculus.continuousOn_out_section h.solution.cont_phi hs).norm
  have cF : ContinuousOn (fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) (Icc a 0) :=
    ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
      (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')).norm
  let f1 := fun v => ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 3 / S.r u v ^ 2 * S.lam u v
  let f2 := fun v => terminalMass S u * ‖S.theta u v / (S.lam u v : ℂ)‖ /
    S.r u v ^ 3 * S.lam u v
  let f3 := fun v => |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 *
    ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v
  let f4 := fun v => |e| * |S.Q u v| / S.r u v ^ 2 *
    ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v
  let f5 := fun v => |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 * S.lam u v
  let f6 := fun v => e ^ 2 * ‖S.phi u v‖ ^ 2 *
    ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v
  have c1 : ContinuousOn f1 (Icc a 0) := by
    dsimp [f1]; exact ((cF.pow 3).div (cr.pow 2)
      (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl
  have c2 : ContinuousOn f2 (Icc a 0) := by
    dsimp [f2]; exact ((cF.const_mul _).div (cr.pow 3)
      (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl
  have c3 : ContinuousOn f3 (Icc a 0) := by
    dsimp [f3]; exact ((((cq.const_mul _).mul cp).div (cr.pow 2)
      (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul (cF.pow 2)).mul cl
  have c4 : ContinuousOn f4 (Icc a 0) := by
    dsimp [f4]; exact (((cq.const_mul _).div (cr.pow 2)
      (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cF).mul cl
  have c5 : ContinuousOn f5 (Icc a 0) := by
    dsimp [f5]; exact (((cq.const_mul _).mul cp).div (cr.pow 2)
      (fun v hv => pow_ne_zero _ (hr v hv).ne')).mul cl
  have c6 : ContinuousOn f6 (Icc a 0) := by
    dsimp [f6]; exact (((cp.pow 2).const_mul _).mul cF).mul cl
  have i1 := c1.intervalIntegrable_of_Icc (μ := volume) ha
  have i2 := c2.intervalIntegrable_of_Icc (μ := volume) ha
  have i3 := c3.intervalIntegrable_of_Icc (μ := volume) ha
  have i4 := c4.intervalIntegrable_of_Icc (μ := volume) ha
  have i5 := c5.intervalIntegrable_of_Icc (μ := volume) ha
  have i6 := c6.intervalIntegrable_of_Icc (μ := volume) ha
  have cSrc : ContinuousOn (fun v => ‖rawDensitySource e S u v‖) (Icc a 0) := by
    apply ContinuousOn.norm
    exact (Calculus.continuousOn_rawDensitySource h.solution
      (show outSeg u a 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} from
        fun p hp => ⟨hs hp, by rcases hp with ⟨rfl, hp⟩; exact hua.trans_le hp.1⟩)).comp
      (f := fun v : ℝ => (u, v))
      (continuousOn_const.prodMk continuousOn_id) (fun v hv => ⟨rfl, hv⟩)
  have iSrc := cSrc.intervalIntegrable_of_Icc (μ := volume) ha
  have iSum := (((((i1.const_mul 65).add (i2.const_mul 326)).add
    (i3.const_mul 3)).add (i4.const_mul 3)).add i5).add i6
  have hM : 0 ≤ terminalMass S u := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hn : 0 ≤ -S.nu u 0 := (neg_pos.mpr
    (h.solution.nu_neg (u, 0) (hs ⟨rfl, ha, le_rfl⟩))).le
  have hL : 0 ≤ L := (norm_nonneg _).trans (hphi a ⟨le_rfl, ha⟩)
  have hSF : 0 ≤ SF := (norm_nonneg _).trans (hF a ⟨le_rfl, ha⟩)
  have hagg : (∫ v in a..0, ‖rawDensitySource e S u v‖) ≤
      4 * (-S.nu u 0) * (65 * (∫ v in a..0, f1 v) +
      326 * (∫ v in a..0, f2 v) + 3 * (∫ v in a..0, f3 v) +
      3 * (∫ v in a..0, f4 v) + (∫ v in a..0, f5 v) + ∫ v in a..0, f6 v) := by
    calc
      _ ≤ ∫ v in a..0, 4 * (-S.nu u 0) *
          (65 * f1 v + 326 * f2 v + 3 * f3 v + 3 * f4 v + f5 v + f6 v) := by
        apply intervalIntegral.integral_mono_on ha iSrc (iSum.const_mul _)
        intro v hv
        apply rawDensitySource_norm_le_of_profiles h (hs ⟨rfl, hv⟩)
          (hua.trans_le hv.1) (hg v hv) _ (hQ v hv) (hnu v hv)
        have hrl := outgoing_radius_mono h hua.le hv.1
          (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
        exact (div_le_div_of_nonneg_left hM (hr a ⟨le_rfl, ha⟩) hrl).trans hX
      _ = _ := by
        rw [intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_add (((((i1.const_mul 65).add (i2.const_mul 326)).add
          (i3.const_mul 3)).add (i4.const_mul 3)).add i5) i6]
        rw [intervalIntegral.integral_add ((((i1.const_mul 65).add (i2.const_mul 326)).add
          (i3.const_mul 3)).add (i4.const_mul 3)) i5]
        rw [intervalIntegral.integral_add (((i1.const_mul 65).add (i2.const_mul 326)).add
          (i3.const_mul 3)) (i4.const_mul 3)]
        rw [intervalIntegral.integral_add ((i1.const_mul 65).add (i2.const_mul 326))
          (i3.const_mul 3)]
        rw [intervalIntegral.integral_add (i1.const_mul 65) (i2.const_mul 326)]
        simp only [intervalIntegral.integral_const_mul]
  have b1 := source_neutral_cubic_bound_of_profiles h hua ha hs hg hF
  have b2 := source_mass_bound_of_gap h hua ha hs hg
  have b3 := source_cubic_charge_bound_of_profiles h hua ha hs hg hphi hQ
  have b4 := source_linear_charge_bound_of_gap h hua ha hs hg
  have b5 := source_scalar_charge_bound_of_envelope h hua ha hs hphi
  have b6 := source_quadratic_coupling_bound_of_gap h hua ha hs hg hphi
  change (∫ v in a..0, f1 v) ≤ _ at b1
  change (∫ v in a..0, f2 v) ≤ _ at b2
  change (∫ v in a..0, f3 v) ≤ _ at b3
  change (∫ v in a..0, f4 v) ≤ _ at b4
  change (∫ v in a..0, f5 v) ≤ _ at b5
  change (∫ v in a..0, f6 v) ≤ _ at b6
  have hb := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left b1 (by norm_num : (0:ℝ) ≤ 65))
      (mul_le_mul_of_nonneg_left b2 (by norm_num : (0:ℝ) ≤ 326)))
      (mul_le_mul_of_nonneg_left b3 (by norm_num : (0:ℝ) ≤ 3)))
      (mul_le_mul_of_nonneg_left b4 (by norm_num : (0:ℝ) ≤ 3))) b5) b6)
    (show 0 ≤ 4 * (-S.nu u 0) by positivity)
  refine hagg.trans (hb.trans ?_)
  have ha2 : 0 ≤ terminalMass S u / S.r u a ^ 2 := by positivity
  have hx0 : 0 ≤ terminalMass S u / S.r u a := div_nonneg hM (hr a ⟨le_rfl, ha⟩).le
  have hR : 0 ≤ terminalRadius S u := (hr 0 ⟨ha, le_rfl⟩).le
  have hn1 := mul_nonneg hn (mul_nonneg ha2 hSF)
  have hn2 := mul_nonneg hn (mul_nonneg ha2
    (Real.sqrt_nonneg (terminalMass S u / S.r u a)))
  have hn3 : 0 ≤ (-S.nu u 0) * (|e| * L * (terminalMass S u / S.r u a) *
      Real.sqrt (terminalMass S u / S.r u a)) := by positivity
  have hn4 : 0 ≤ (-S.nu u 0) * (|e| * (terminalMass S u / S.r u a)) := by positivity
  have hn5 : 0 ≤ (-S.nu u 0) * (|e| * L * Real.sqrt (terminalMass S u / S.r u a)) := by positivity
  have hn6 : 0 ≤ (-S.nu u 0) * (e ^ 2 * L ^ 2 *
      Real.sqrt (terminalMass S u * terminalRadius S u)) := by positivity
  have hnum := numerical_source_sum hn1 hn2 hn3 hn4 hn5 hn6
  convert hnum using 1 <;> ring

end EmcsfAcExtension.Global.Exterior
