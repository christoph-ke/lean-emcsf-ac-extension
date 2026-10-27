module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Classical limits at the regular axis

Radial averages of continuous partials identify the limits of quotients by the
radius. The mass equation is used only off the axis, after boundedness of the
mass ratio and vanishing of the charge ratio have been established.
-/

public section

open Set Filter MeasureTheory Topology Complex

namespace EmcsfAcExtension.Local

private theorem triangle_subset_closure_offAxis {a b : ℝ} (hab : a < b) :
    triangle a b ⊆ closure (triangle a b ∩ {p | p.1 < p.2}) := by
  intro p hp
  have hq : (a, b) ∈ triangle a b := ⟨le_rfl, hab.le, le_rfl⟩
  have hs : openSegment ℝ p (a, b) ⊆ triangle a b ∩ {p | p.1 < p.2} := by
    rintro q ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨(convex_triangle a b) hp hq hs.le ht.le hst,
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hp.2.1 hs.le)
        (mul_lt_mul_of_pos_left hab ht)⟩
  exact (closure_mono hs) (segment_subset_closure_openSegment (left_mem_segment ℝ p (a, b)))

/-- Continuous identities off the axis extend to the entire nondegenerate triangle. -/
theorem eqOn_triangle_of_offAxis {E : Type*} [TopologicalSpace E] [T2Space E]
    {a b : ℝ} (hab : a < b) {f g : ℝ × ℝ → E}
    (hf : ContinuousOn f (triangle a b)) (hg : ContinuousOn g (triangle a b))
    (heq : ∀ p ∈ triangle a b, p.1 < p.2 → f p = g p) : EqOn f g (triangle a b) :=
  (show EqOn f g (triangle a b ∩ {p | p.1 < p.2}) from
    fun p hp => heq p hp.1 hp.2).of_subset_closure hf hg inter_subset_left
      (triangle_subset_closure_offAxis hab)

private noncomputable def radialMean (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, f (p.1, p.1 + (p.2 - p.1) * s)

private def radialProj (a b : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (min (max a p.1) b, max (min (max a p.1) b) (min p.2 b))

private theorem continuousOn_radialMean {a b : ℝ} (hab : a ≤ b) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f (triangle a b)) : ContinuousOn (radialMean f) (triangle a b) := by
  have cP : Continuous (radialProj a b) := by unfold radialProj; fun_prop
  have mP : ∀ p, radialProj a b p ∈ triangle a b := fun p =>
    ⟨le_min (le_max_left _ _) hab, le_max_left _ _,
      max_le (min_le_right _ _) (min_le_right _ _)⟩
  have fixP : ∀ p ∈ triangle a b, radialProj a b p = p := by
    intro p hp
    dsimp [radialProj]
    rw [max_eq_right hp.1, min_eq_left (hp.2.1.trans hp.2.2),
      min_eq_left hp.2.2, max_eq_right hp.2.1]
  have ce : Continuous (f ∘ radialProj a b) := hf.comp_continuous cP mP
  have cc : Continuous (fun z : (ℝ × ℝ) × ℝ =>
      (z.1.1, z.1.1 + (z.1.2 - z.1.1) * z.2)) := by fun_prop
  have ci : Continuous (fun p : ℝ × ℝ => ∫ s in (0 : ℝ)..1,
      f (radialProj a b (p.1, p.1 + (p.2 - p.1) * s))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (s : ℝ) =>
        f (radialProj a b (p.1, p.1 + (p.2 - p.1) * s)))
      (ce.comp cc) continuous_const
  apply ci.continuousOn.congr
  intro p hp
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
  have hnon : 0 ≤ (p.2 - p.1) * s := mul_nonneg (sub_nonneg.mpr hp.2.1) hs.1
  have hle : (p.2 - p.1) * s ≤ p.2 - p.1 :=
    mul_le_of_le_one_right (sub_nonneg.mpr hp.2.1) hs.2
  change f (p.1, p.1 + (p.2 - p.1) * s) =
    f (radialProj a b (p.1, p.1 + (p.2 - p.1) * s))
  rw [fixP (p.1, p.1 + (p.2 - p.1) * s)
    ⟨hp.1, by dsimp; linarith, by dsimp; linarith [hp.2.2]⟩]

private theorem radialMean_axis (f : ℝ × ℝ → ℝ) (t : ℝ) :
    radialMean f (t, t) = f (t, t) := by simp [radialMean]

private theorem mul_radialMean_pdV {a b : ℝ} (hab : a < b) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (hz : ∀ t ∈ Icc a b, f t t = 0) {u v : ℝ} (hp : (u, v) ∈ triangle a b) :
    (v - u) * radialMean (Function.uncurry (pdV (triangle a b) f)) (u, v) = f u v := by
  have hi := integralForm_pdV hf (uniqueDiffOn_triangle hab) hp.2.1
    (fun x hx => (show (u, x) ∈ triangle a b from ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩))
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (pdV (triangle a b) f u) (v - u) u (a := 0) (b := 1)
  have hmean : (v - u) * radialMean (Function.uncurry (pdV (triangle a b) f)) (u, v) =
      ∫ x in u..v, pdV (triangle a b) f u x := by
    simpa only [radialMean, Function.uncurry_apply_pair, smul_eq_mul,
      mul_zero, add_zero, mul_one, add_sub_cancel] using hchange
  rw [hmean, ← hi.2, hz u ⟨hp.1, hp.2.1.trans hp.2.2⟩, sub_zero]

/-- The quotient of two C¹ fields vanishing along the diagonal tends to the
quotient of their outgoing partials wherever the latter denominator is nonzero. -/
theorem tendsto_axis_quotient {a b t : ℝ} (hab : a < b) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) (triangle a b))
    (hf0 : ∀ s ∈ Icc a b, f s s = 0) (hg0 : ∀ s ∈ Icc a b, g s s = 0)
    (ht : t ∈ Icc a b) (hden : pdV (triangle a b) g t t ≠ 0) :
    Tendsto (fun p : ℝ × ℝ => f p.1 p.2 / g p.1 p.2)
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t))
      (𝓝 (pdV (triangle a b) f t t / pdV (triangle a b) g t t)) := by
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  have cf := continuousOn_radialMean hab.le (continuousOn_pdV hf (uniqueDiffOn_triangle hab))
  have cg := continuousOn_radialMean hab.le (continuousOn_pdV hg (uniqueDiffOn_triangle hab))
  have hc := (cf (t, t) hp).div (cg (t, t) hp) (by simpa [radialMean_axis] using hden)
  have hl := hc.mono (show triangle a b ∩ {p | p.1 < p.2} ⊆ triangle a b from
    inter_subset_left)
  simp only [ContinuousWithinAt, Pi.div_apply, radialMean_axis] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  rw [← mul_radialMean_pdV hab hf hf0 hp.1, ← mul_radialMean_pdV hab hg hg0 hp.1]
  exact (mul_div_mul_left _ _ (show p.2 - p.1 ≠ 0 from sub_ne_zero.mpr hp.2.ne')).symm

variable {a b e : ℝ} {S : Fields}

/-- The classical outgoing radius equation extends continuously to the axis. -/
theorem IsC1Solution.pdV_r (hS : IsC1Solution e S (triangle a b)) (hab : a < b)
    {u v : ℝ} (hp : (u, v) ∈ triangle a b) :
    pdV (triangle a b) S.r u v = S.lam u v :=
  eqOn_triangle_of_offAxis hab (continuousOn_pdV hS.c1_r (uniqueDiffOn_triangle hab))
    hS.c1_lam.continuousOn (fun p hp huv => (hS.eq_v p hp huv).1) hp

/-- The outgoing charge partial vanishes at every axis point, including both corners. -/
theorem IsC1Solution.pdV_Q_axis (hS : IsC1Solution e S (triangle a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) : pdV (triangle a b) S.Q t t = 0 := by
  have cq : ContinuousOn (Function.uncurry (S.QV e)) (triangle a b) := by
    exact (continuousOn_const.mul hS.c1_r.continuousOn |>.mul
      (Complex.continuous_im.comp_continuousOn
        (hS.c1_phi.continuousOn.star.mul hS.c1_theta.continuousOn))).neg
  have heq := eqOn_triangle_of_offAxis hab
    (continuousOn_pdV hS.c1_Q (uniqueDiffOn_triangle hab)) cq
    (fun p hp huv => (hS.eq_v p hp huv).2.2.2.1)
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  have heq' : pdV (triangle a b) S.Q t t = S.QV e t t := heq hp
  simpa only [Fields.QV, (hS.axis t hp).1, mul_zero, zero_mul, neg_zero] using heq'

/-- The classical charge satisfies `Q = o(r)` at every existing axis point. -/
theorem IsC1Solution.axis_Q_div_r (hS : IsC1Solution e S (triangle a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Tendsto (fun p : ℝ × ℝ => S.Q p.1 p.2 / S.r p.1 p.2)
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) := by
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  simpa only [hS.pdV_Q_axis hab ht, zero_div] using tendsto_axis_quotient hab
    hS.c1_Q hS.c1_r
    (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.2.1)
    (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).1) ht
    (by rw [hS.pdV_r hab hp]; exact ne_of_gt (hS.lam_pos _ hp))

/-- The classical outgoing normalized scalar defect vanishes on the axis. -/
theorem IsC1Solution.theta_axis (hS : IsC1Solution e S (triangle a b))
    {t : ℝ} (ht : t ∈ Icc a b) : S.theta t t = 0 := by
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  have ha := (hS.axis t hp).2.2.2.2.1
  have hn : (S.lam t t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (hS.lam_pos _ hp))
  simpa only [Fields.a, add_eq_left, div_eq_zero_iff, or_iff_left hn] using ha

/-- The classical mass ratio tends to zero at every axis point. This is exactly
the `axis_mu` clause required by the frozen solution class. -/
theorem IsC1Solution.axis_mu (hS : IsC1Solution e S (triangle a b)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    Tendsto (Function.uncurry S.mu)
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) := by
  let F := 𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  have : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp
    (triangle_subset_closure_offAxis hab hp)
  have hn : S.lam t t ≠ 0 := ne_of_gt (hS.lam_pos _ hp)
  have hm := tendsto_axis_quotient hab hS.c1_m hS.c1_r
    (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.1)
    (fun s hs => (hS.axis s ⟨hs.1, le_rfl, hs.2⟩).1) ht
    (by rw [hS.pdV_r hab hp]; exact hn)
  rw [hS.pdV_r hab hp] at hm
  have hmu : Tendsto (Function.uncurry S.mu) F
      (𝓝 (2 * (pdV (triangle a b) S.m t t / S.lam t t))) := by
    change Tendsto (fun p : ℝ × ℝ => 2 * S.m p.1 p.2 / S.r p.1 p.2) F _
    simpa only [mul_div_assoc] using hm.const_mul 2
  have hl : Tendsto (Function.uncurry S.lam) F (𝓝 (S.lam t t)) :=
    (hS.c1_lam.continuousOn _ hp).mono inter_subset_left
  have htheta : Tendsto (Function.uncurry S.theta) F (𝓝 0) := by
    rw [← hS.theta_axis ht]
    exact (hS.c1_theta.continuousOn _ hp).mono inter_subset_left
  have hq := hS.axis_Q_div_r hab ht
  have hsource : Tendsto (fun p : ℝ × ℝ =>
      (1 - S.mu p.1 p.2) * ‖S.theta p.1 p.2‖ ^ 2 / (2 * S.lam p.1 p.2) +
        (S.Q p.1 p.2 / S.r p.1 p.2) ^ 2 * S.lam p.1 p.2 / 2) F (𝓝 0) := by
    convert ((((tendsto_const_nhds (x := (1 : ℝ))).sub hmu).mul (htheta.norm.pow 2)).div
      (hl.const_mul 2) (mul_ne_zero (by norm_num) hn)).add
      (((hq.pow 2).mul hl).div_const 2) using 1 <;> norm_num [Function.uncurry_def]
  have hd : Tendsto (Function.uncurry (pdV (triangle a b) S.m)) F
      (𝓝 (pdV (triangle a b) S.m t t)) :=
    ((continuousOn_pdV hS.c1_m (uniqueDiffOn_triangle hab)) _ hp).mono inter_subset_left
  have heq : (fun p : ℝ × ℝ =>
      (1 - S.mu p.1 p.2) * ‖S.theta p.1 p.2‖ ^ 2 / (2 * S.lam p.1 p.2) +
        (S.Q p.1 p.2 / S.r p.1 p.2) ^ 2 * S.lam p.1 p.2 / 2) =ᶠ[F]
        Function.uncurry (pdV (triangle a b) S.m) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    change _ = pdV (triangle a b) S.m p.1 p.2
    rw [(hS.eq_v p hp.1 hp.2).2.2.1]
    unfold Fields.mV
    congr 1
    ring
  have hz : pdV (triangle a b) S.m t t = 0 :=
    tendsto_nhds_unique hd (hsource.congr' heq)
  simpa only [hz, zero_div, mul_zero] using hmu

end EmcsfAcExtension.Local
