module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.AxisLimits
import EmcsfAcExtension.Local.Algebra.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Classical derivatives at the diagonal

Auxiliary diagonal calculus for `charged_SF_new_version.tex:L6453–6459`. The outgoing
transport of the incoming normalized field vanishes at the regular center.
Only within-triangle derivatives are evaluated at the axis.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology

namespace EmcsfAcExtension.Local

private theorem b_partial_v {e T u v : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
    pdV (triangle 0 T) S.b u v = (-(S.lam u v : ℂ) / S.r u v) *
      (((S.mu u v : ℂ) - (S.Q u v : ℂ) ^ 2 / (S.r u v : ℂ) ^ 2) /
        (1 - S.mu u v) * (S.xi u v / S.nu u v) -
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) := by
  have hn : (S.nu u v : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
  have hd := (hasDerivWithinAt_triangle_v hS.c1_phi hp).add
    ((hasDerivWithinAt_triangle_v hS.c1_xi hp).div
      (hasDerivWithinAt_triangle_v hS.c1_nu hp).ofReal_comp hn)
  have hb := hasDerivWithinAt_triangle_v hS.c1_b hp
  have huDiff := uniqueDiffOn_Icc (huv.trans_le hp.2.2) v ⟨huv.le, hp.2.2⟩
  have heq := (hb.derivWithin huDiff).symm.trans (hd.derivWithin huDiff)
  change pdV (triangle 0 T) S.b u v = _ at heq
  rw [heq]
  apply eq_normalized_out_algebra (hS.r_pos _ hp huv).ne' (hS.nu_neg _ hp).ne
    (hS.one_sub_mu_pos _ hp).ne'
  · exact (hS.eq_v _ hp huv).2.1
  · exact (hS.eq_v _ hp huv).2.2.2.2.2.1
  · exact (hS.eq_v _ hp huv).2.2.2.2.2.2

/-- The outgoing partial of the incoming normalized scalar vanishes on the
regular axis. This auxiliary classical identity includes both triangle corners
and requires no quantitative bound on derivatives. -/
theorem IsC1Solution.pdV_b_axis {e T t : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T) (ht : t ∈ Icc 0 T) :
    pdV (triangle 0 T) S.b t t = 0 := by
  let F := 𝓝[triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hne : F.NeBot := by
    have hsub : triangle 0 T ⊆ closure (triangle 0 T ∩ {p | p.1 < p.2}) := by
      intro p hp
      have hq : ((0 : ℝ), T) ∈ triangle 0 T := ⟨le_rfl, hT.le, le_rfl⟩
      have hs : openSegment ℝ p (0, T) ⊆ triangle 0 T ∩ {p | p.1 < p.2} := by
        rintro q ⟨s, t, hs, ht, hst, rfl⟩
        exact ⟨(convex_triangle 0 T) hp hq hs.le ht.le hst,
          add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hp.2.1 hs.le)
            (mul_lt_mul_of_pos_left hT ht)⟩
      exact (closure_mono hs)
        (segment_subset_closure_openSegment (left_mem_segment ℝ p (0, T)))
    exact mem_closure_iff_nhdsWithin_neBot.mp (hsub hp)
  have hlam : Tendsto (fun p : ℝ × ℝ => (S.lam p.1 p.2 : ℂ)) F (𝓝 (S.lam t t : ℂ)) :=
    (Complex.continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn _ hp).mono inter_subset_left
  have hphi : Tendsto (Function.uncurry S.phi) F (𝓝 (S.phi t t)) :=
    (hS.c1_phi.continuousOn _ hp).mono inter_subset_left
  have hmu : Tendsto (fun p : ℝ × ℝ => (S.mu p.1 p.2 : ℂ)) F (𝓝 0) := by
    simpa only [F, Function.comp_def, Function.uncurry_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hS.axis_mu hT ht)
  have hq : Tendsto (fun p : ℝ × ℝ => (S.Q p.1 p.2 : ℂ) / S.r p.1 p.2) F (𝓝 0) := by
    simpa only [F, Function.comp_def, Complex.ofReal_div, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hS.axis_Q_div_r hT ht)
  have hnu : (S.nu t t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
  have hratio : Tendsto (fun p : ℝ × ℝ => S.xi p.1 p.2 / S.nu p.1 p.2 / S.r p.1 p.2)
      F (𝓝 ((pdU (triangle 0 T) S.phi t t + I * e * S.A t t * S.phi t t) / S.nu t t)) := by
    have hh := (((continuousOn_pdU hS.c1_phi (uniqueDiffOn_triangle hT)).add
      (((continuousOn_const (c := I * (e : ℂ))).mul (Complex.continuous_ofReal.comp_continuousOn
        hS.c1_A.continuousOn)).mul hS.c1_phi.continuousOn)) _ hp).div
          (Complex.continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn _ hp) hnu
    apply (hh.mono inter_subset_left).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, Function.comp_apply,
      Function.uncurry_def]
    rw [(hS.eq_u p hp.1 hp.2).2.2.2.2.1]
    unfold Fields.phiU
    ring
  have hsource : Tendsto (fun p : ℝ × ℝ =>
      (-(S.lam p.1 p.2 : ℂ) / (1 - S.mu p.1 p.2)) *
        (((S.mu p.1 p.2 : ℂ) - ((S.Q p.1 p.2 : ℂ) / S.r p.1 p.2) ^ 2) *
          (S.xi p.1 p.2 / S.nu p.1 p.2 / S.r p.1 p.2) -
            I * e * ((S.Q p.1 p.2 : ℂ) / S.r p.1 p.2) * S.phi p.1 p.2)) F (𝓝 0) := by
    have hg : Tendsto (fun p : ℝ × ℝ => 1 - (S.mu p.1 p.2 : ℂ)) F (𝓝 (1 : ℂ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℂ))).sub hmu
    have hz := ((hmu.sub (hq.pow 2)).mul hratio).sub
      (((tendsto_const_nhds (x := I * (e : ℂ))).mul hq).mul hphi)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_self, sub_zero,
      zero_mul, mul_zero, Pi.div_apply, Function.uncurry_def] using
        (hlam.neg.div hg one_ne_zero).mul hz
  have hevent : (fun p : ℝ × ℝ =>
      (-(S.lam p.1 p.2 : ℂ) / (1 - S.mu p.1 p.2)) *
        (((S.mu p.1 p.2 : ℂ) - ((S.Q p.1 p.2 : ℂ) / S.r p.1 p.2) ^ 2) *
          (S.xi p.1 p.2 / S.nu p.1 p.2 / S.r p.1 p.2) -
            I * e * ((S.Q p.1 p.2 : ℂ) / S.r p.1 p.2) * S.phi p.1 p.2)) =ᶠ[F]
        Function.uncurry (pdV (triangle 0 T) S.b) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    change _ = pdV (triangle 0 T) S.b p.1 p.2
    rw [b_partial_v hS hp.1 hp.2]
    have hr : (S.r p.1 p.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.r_pos p hp.1 hp.2).ne'
    have hn : (S.nu p.1 p.2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.nu_neg p hp.1).ne
    have hg : (1 - (S.mu p.1 p.2 : ℂ)) ≠ 0 := by
      exact_mod_cast (hS.one_sub_mu_pos p hp.1).ne'
    field_simp [hr, hn, hg]
  exact tendsto_nhds_unique
    (((continuousOn_pdV hS.c1_b (uniqueDiffOn_triangle hT)) _ hp).mono inter_subset_left)
      (hsource.congr' hevent)

/-- The ordinary diagonal scalar derivative is the incoming classical
renormalized density in the zero-axis gauge. Endpoint derivatives are taken
within `[0,T]`; the identity gives ordinary derivatives at its interior. -/
theorem IsC1Solution.axis_hasDerivWithinAt {e T t : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) (hT : 0 < T)
    (hA : ∀ t ∈ Icc 0 T, S.A t t = 0) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => S.phi s s) (kC1 e (triangle 0 T) S t t) (Icc 0 T) t := by
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hd : HasDerivWithinAt (fun s => S.b s s)
      (fderivWithin ℝ (Function.uncurry S.b) (triangle 0 T) (t, t) (1, 1)) (Icc 0 T) t :=
    ((hS.c1_b.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt).comp_hasDerivWithinAt
    (f := fun s : ℝ => (s, s)) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt)
    (fun s (hs : s ∈ Icc 0 T) => (show (s, s) ∈ triangle 0 T from ⟨hs.1, le_rfl, hs.2⟩))
  have hk : kC1 e (triangle 0 T) S t t = pdU (triangle 0 T) S.b t t := by
    simp [kC1, Fields.mu, (hS.axis t hp).1, hA t ht]
  have hval : fderivWithin ℝ (Function.uncurry S.b) (triangle 0 T) (t, t) (1, 1) =
      kC1 e (triangle 0 T) S t t := by
    rw [show ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) by ext <;> norm_num,
      map_add]
    change pdU (triangle 0 T) S.b t t + pdV (triangle 0 T) S.b t t = _
    rw [hS.pdV_b_axis hT ht, add_zero, hk]
  exact (hd.congr_deriv hval).congr_of_mem
    (fun s hs => ((hS.axis s ⟨hs.1, le_rfl, hs.2⟩).2.2.2.2.2).symm) ht

end EmcsfAcExtension.Local
