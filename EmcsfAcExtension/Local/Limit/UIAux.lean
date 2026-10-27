module

public import EmcsfAcExtension.Local.Defs.Limit
import EmcsfAcExtension.Local.Calculus.AxisLimits
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Continuous classical representatives of the renormalized derivatives

The apparent divisions by the radius in the cubic corrections are removable
at the regular axis. These lemmas supply the continuous representatives used
by internal project record A5, before any limiting derivative has been identified.
-/

public section

open Set Filter Topology Complex

namespace EmcsfAcExtension.Local

/-- The classical mass ratio is continuous on the whole nondegenerate triangle,
including its frozen zero value on the axis. No quantitative constant occurs. -/
theorem IsC1Solution.continuousOn_mu {e a b : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) (hab : a < b) :
    ContinuousOn (Function.uncurry S.mu) (triangle a b) := by
  intro ⟨u, v⟩ hp
  have hle : u ≤ v := hp.2.1
  rcases hle.eq_or_lt with heq | hlt
  · have hp' : v ∈ Icc a b := ⟨heq ▸ hp.1, hp.2.2⟩
    have hzero : S.mu u v = 0 := by
      simp [Fields.mu, heq, (hS.axis v ⟨hp'.1, le_rfl, hp'.2⟩).1]
    have hoff : ContinuousWithinAt (Function.uncurry S.mu)
        (triangle a b ∩ {q | q.1 < q.2}) (u, v) := by
      change Tendsto _ _ (𝓝 (S.mu u v))
      rw [hzero]
      simpa only [heq] using hS.axis_mu hab hp'
    have hdiag : ContinuousWithinAt (Function.uncurry S.mu)
        (triangle a b ∩ {q | q.1 = q.2}) (u, v) := by
      change Tendsto _ _ (𝓝 (S.mu u v))
      rw [hzero]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      have he : q.1 = q.2 := hq.2
      change (0 : ℝ) = S.mu q.1 q.2
      rw [he]
      simp [Fields.mu, (hS.axis q.2
        ⟨he ▸ hq.1.1, le_rfl, hq.1.2.2⟩).1]
    apply (hoff.union hdiag).mono
    intro q hq
    rcases hq.2.1.eq_or_lt with h | h
    · exact Or.inr ⟨hq, h⟩
    · exact Or.inl ⟨hq, h⟩
  · exact ((hS.c1_m.continuousOn (u, v) hp).const_mul 2).div
      (hS.c1_r.continuousOn (u, v) hp) (hS.r_pos (u, v) hp hlt).ne'

private theorem outgoing_cubic_eq {e a b u v : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) (hp : (u, v) ∈ triangle a b) :
    (S.lam u v / S.r u v : ℂ) * ‖S.theta u v / S.lam u v‖ ^ 2 *
        (S.theta u v / S.lam u v) =
      (‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) * pdV (triangle a b) S.phi u v := by
  have hle : u ≤ v := hp.2.1
  rcases hle.eq_or_lt with rfl | huv
  · rw [hS.theta_axis ⟨hp.1, hp.2.2⟩]
    simp
  · rw [(hS.eq_v (u, v) hp huv).2.2.2.2.2.1]
    unfold Fields.phiV
    have hl : (S.lam u v : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.lam_pos _ hp).ne'
    push_cast
    field_simp [hl]

/-- The classical outgoing renormalized derivative has a continuous representative
on the closed triangle. Axis regularity removes its cubic radius denominator. -/
theorem IsC1Solution.continuousOn_jC1 {e a b : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) (hab : a < b) :
    ContinuousOn (Function.uncurry (jC1 (triangle a b) S)) (triangle a b) := by
  have hx : ContinuousOn (fun p : ℝ × ℝ => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ))
      (triangle a b) := hS.c1_theta.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn)
    (fun p hp => ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')
  have hh := (Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_const (c := (1 : ℝ))).sub (hS.continuousOn_mu hab))).mul
      ((continuousOn_pdV hS.c1_a (uniqueDiffOn_triangle hab)).sub
        ((Complex.continuous_ofReal.comp_continuousOn (hx.norm.pow 2)).mul
          (continuousOn_pdV hS.c1_phi (uniqueDiffOn_triangle hab))))
  apply hh.congr
  intro p hp
  change jC1 (triangle a b) S p.1 p.2 = _
  unfold jC1
  rw [outgoing_cubic_eq hS hp]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Function.comp_apply, Function.uncurry_def,
    Complex.ofReal_sub, Complex.ofReal_one]

private theorem incoming_cubic_eq {e a b u v : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) (hp : (u, v) ∈ triangle a b) :
    (S.nu u v / S.r u v : ℂ) * ‖S.xi u v / S.nu u v‖ ^ 2 *
        (S.xi u v / S.nu u v) =
      (‖S.xi u v / S.nu u v‖ ^ 2 : ℝ) *
        (pdU (triangle a b) S.phi u v + I * e * S.A u v * S.phi u v) := by
  have hle : u ≤ v := hp.2.1
  rcases hle.eq_or_lt with rfl | huv
  · have hz := (hS.axis u hp).2.2.2.2.2
    have hn : (S.nu u u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
    have hxi : S.xi u u = 0 := by
      simpa only [Fields.b, add_eq_left, div_eq_zero_iff, or_iff_left hn] using hz
    rw [hxi]
    simp
  · rw [(hS.eq_u (u, v) hp huv).2.2.2.2.1]
    unfold Fields.phiU
    have hn : (S.nu u v : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hS.nu_neg _ hp).ne
    push_cast
    field_simp [hn]
    ring

/-- The classical incoming renormalized derivative has a continuous representative
on the closed triangle. The connection term is retained with its own coupling. -/
theorem IsC1Solution.continuousOn_kC1 {e a b : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle a b)) (hab : a < b) :
    ContinuousOn (Function.uncurry (kC1 e (triangle a b) S)) (triangle a b) := by
  have hy : ContinuousOn (fun p : ℝ × ℝ => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
      (triangle a b) := hS.c1_xi.continuousOn.div
    (Complex.continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn)
    (fun p hp => ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)
  have hA : ContinuousOn (fun p : ℝ × ℝ => I * e * S.A p.1 p.2 * S.phi p.1 p.2)
      (triangle a b) := ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul
          hS.c1_phi.continuousOn)
  have hB : ContinuousOn (fun p : ℝ × ℝ => I * e * S.A p.1 p.2 * S.b p.1 p.2)
      (triangle a b) := ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul
          hS.c1_b.continuousOn)
  have hh := (Complex.continuous_ofReal.comp_continuousOn
    ((continuousOn_const (c := (1 : ℝ))).sub (hS.continuousOn_mu hab))).mul
      (((continuousOn_pdU hS.c1_b (uniqueDiffOn_triangle hab)).add hB).sub
        ((Complex.continuous_ofReal.comp_continuousOn (hy.norm.pow 2)).mul
          ((continuousOn_pdU hS.c1_phi (uniqueDiffOn_triangle hab)).add hA)))
  apply hh.congr
  intro p hp
  change kC1 e (triangle a b) S p.1 p.2 = _
  unfold kC1
  rw [incoming_cubic_eq hS hp]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.pow_apply, Function.comp_apply,
    Function.uncurry_def, Complex.ofReal_sub, Complex.ofReal_one]

end EmcsfAcExtension.Local
