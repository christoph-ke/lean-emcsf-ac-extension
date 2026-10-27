module

public import EmcsfAcExtension.Local.Defs.C1Bound
public import EmcsfAcExtension.Local.Defs.Setting

/-! # Assembling the full continuation norm from characteristic bounds

internal project record asks for full operator norms of the within-domain derivatives.
The domain carries the product max norm, so two coordinate partial bounds
give an operator bound with the universal factor two. No compactness bound
for an individual solution is substituted for a uniform datum bound.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The full within-domain derivative is controlled by its two characteristic
partials. The coefficient is exactly one in the sum, independent of the
domain, field and point. This is linear algebra and needs no regularity or
nondegeneracy of the domain. -/
theorem smooth_fderiv_norm_le_partials_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (D : Set (ℝ × ℝ)) (f : ℝ → ℝ → E) (p : ℝ × ℝ) :
    ‖fderivWithin ℝ (Function.uncurry f) D p‖ ≤
      ‖pdU D f p.1 p.2‖ + ‖pdV D f p.1 p.2‖ := by
  let L := fderivWithin ℝ (Function.uncurry f) D p
  change ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖
  apply L.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hx : x = x.1 • ((1, 0) : ℝ × ℝ) + x.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  calc
    ‖L x‖ = ‖x.1 • L (1, 0) + x.2 • L (0, 1)‖ := by
      conv_lhs => rw [hx, map_add, map_smul, map_smul]
    _ ≤ ‖x.1‖ * ‖L (1, 0)‖ + ‖x.2‖ * ‖L (0, 1)‖ := by
      simpa only [norm_smul] using norm_add_le (x.1 • L (1, 0)) (x.2 • L (0, 1))
    _ ≤ ‖x‖ * ‖L (1, 0)‖ + ‖x‖ * ‖L (0, 1)‖ := by
      gcongr
      · exact norm_fst_le x
      · exact norm_snd_le x
    _ = _ := by ring

/-- Assemble internal project record's `C1BoundOn` from actual field and characteristic
partial estimates. The universal formula `B = 4 + 2A` is independent of all
parameters. In a uniform-family application, choose `A` after the fixed
`T,e,h` and before the subtriangle and solution; the resulting `B` has the
same dependence. This conditional helper has no graph-node tag: the
datum-uniform geometric recovery estimates still have to supply its premises. -/
theorem smooth_c1_bound_of_bound {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hA : 0 ≤ A)
    (hreal : ∀ p ∈ triangle 0 T,
      ∀ f ∈ ({S.r, S.lam, S.nu, S.m, S.Q, S.A} : Set (ℝ → ℝ → ℝ)),
      ‖f p.1 p.2‖ ≤ A ∧ ‖pdU (triangle 0 T) f p.1 p.2‖ ≤ A ∧
        ‖pdV (triangle 0 T) f p.1 p.2‖ ≤ A)
    (hcomplex : ∀ p ∈ triangle 0 T,
      ∀ f ∈ ({S.phi, S.theta, S.xi, S.a, S.b} : Set (ℝ → ℝ → ℂ)),
      ‖f p.1 p.2‖ ≤ A ∧ ‖pdU (triangle 0 T) f p.1 p.2‖ ≤ A ∧
        ‖pdV (triangle 0 T) f p.1 p.2‖ ≤ A) :
    0 < 4 + 2 * A ∧ C1BoundOn S (triangle 0 T) (4 + 2 * A) := by
  have hB : 0 < 4 + 2 * A := by positivity
  have hinv : (4 + 2 * A)⁻¹ ≤ 1 / 4 := by
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ 4 + 2 * A by linarith only [hA])
    norm_num at hi
    exact hi
  refine ⟨hB, ?_⟩
  intro p hp
  have hb := hset.box p hp
  refine ⟨hinv.trans hb.1, hinv.trans hb.2.2.1,
    hinv.trans ((by norm_num : (1 : ℝ) / 4 ≤ 1 / 2).trans hb.2.2.2.2.1), ?_, ?_⟩
  · intro f hf
    obtain ⟨hv, hu, hw⟩ := hreal p hp f hf
    refine ⟨hv.trans (by linarith only [hA]), ?_⟩
    apply (smooth_fderiv_norm_le_partials_aux (triangle 0 T) f p).trans
    linarith only [hu, hw]
  · intro f hf
    obtain ⟨hv, hu, hw⟩ := hcomplex p hp f hf
    refine ⟨hv.trans (by linarith only [hA]), ?_⟩
    apply (smooth_fderiv_norm_le_partials_aux (triangle 0 T) f p).trans
    linarith only [hu, hw]

end EmcsfAcExtension.Local
