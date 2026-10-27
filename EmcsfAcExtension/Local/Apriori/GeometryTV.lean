module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Frozen.Fields.Omega2
import EmcsfAcExtension.Local.Apriori.GeometryTVSame
import EmcsfAcExtension.Local.Apriori.GeometryTVCross
import EmcsfAcExtension.Local.Apriori.GeometryTVMass
import EmcsfAcExtension.Local.Apriori.Charge
import Mathlib.Analysis.BoundedVariation

/-! # The complete geometric characteristic variation budget

The metric coefficient is the literal product and inverse gap
`Ω² = -4νλ/(1-μ)`. Bounded-variation product estimates and the Lipschitz
inverse gap combine the three previously controlled field variations
(`charged_SF_new_version.tex:L4900–L4907`).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem inverse_gap_lipschitz :
    LipschitzOnWith 4 (fun x : ℝ => 1 / (1 - x)) (Iic (1 / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxH : 0 < 1 - x := by change x ≤ 1 / 2 at hx; linarith only [hx]
  have hyH : 0 < 1 - y := by change y ≤ 1 / 2 at hy; linarith only [hy]
  have hd : 1 / 4 ≤ (1 - x) * (1 - y) := by
    have h := mul_le_mul
      (show (1 : ℝ) / 2 ≤ 1 - x by change x ≤ 1 / 2 at hx; linarith only [hx])
      (show (1 : ℝ) / 2 ≤ 1 - y by change y ≤ 1 / 2 at hy; linarith only [hy])
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hxH.le
    norm_num at h
    exact h
  change |1 / (1 - x) - 1 / (1 - y)| ≤ 4 * |x - y|
  have heq : 1 / (1 - x) - 1 / (1 - y) = (x - y) / ((1 - x) * (1 - y)) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos (mul_pos hxH hyH), div_le_iff₀ (mul_pos hxH hyH)]
  have hi := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 * |x - y| by positivity)
  nlinarith only [hi]

/-- Within the fixed geometric box, the metric variation is at most
`8 (TV λ + TV ν) + 16 TV μ`. The coefficients depend only on the expansion
upper bound one and inverse-gap upper bound two, uniformly in all functions,
sets and field parameters. No differentiability hypothesis is needed. -/
theorem metric_variation_le {s : Set ℝ} {l n m : ℝ → ℝ}
    (hl : ∀ x ∈ s, 0 ≤ l x ∧ l x ≤ 1)
    (hn : ∀ x ∈ s, 0 ≤ -n x ∧ -n x ≤ 1)
    (hm : ∀ x ∈ s, 1 / 2 ≤ 1 - m x) :
    eVariationOn (fun x => -4 * n x * l x / (1 - m x)) s ≤
      8 * (eVariationOn l s + eVariationOn n s) + 16 * eVariationOn m s := by
  have hlN (x : ℝ) (hx : x ∈ s) : ‖l x‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hl x hx).1]
    exact (ENNReal.ofReal_le_ofReal (hl x hx).2).trans_eq ENNReal.ofReal_one
  have hnN (x : ℝ) (hx : x ∈ s) : ‖n x‖ₑ ≤ 1 := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonpos (by linarith only [(hn x hx).1])]
    exact (ENNReal.ofReal_le_ofReal (hn x hx).2).trans_eq ENNReal.ofReal_one
  have hiN (x : ℝ) (hx : x ∈ s) : ‖1 / (1 - m x)‖ₑ ≤ 2 := by
    have hH : 0 < 1 - m x := lt_of_lt_of_le (by norm_num) (hm x hx)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hH.le)]
    apply (ENNReal.ofReal_le_ofReal ?_).trans_eq (by norm_num : ENNReal.ofReal (2 : ℝ) = 2)
    apply (div_le_iff₀ hH).mpr
    linarith only [hm x hx]
  have hprodN (x : ℝ) (hx : x ∈ s) : ‖n x * l x‖ₑ ≤ 1 := by
    rw [enorm_mul]
    exact (mul_le_mul' (hnN x hx) (hlN x hx)).trans_eq (by simp)
  have hp : eVariationOn (fun x => n x * l x) s ≤ eVariationOn l s + eVariationOn n s := by
    simpa only [one_mul] using eVariationOn_fun_mul_le hnN hlN
  have hi : eVariationOn (fun x => 1 / (1 - m x)) s ≤ 4 * eVariationOn m s := by
    exact inverse_gap_lipschitz.comp_eVariationOn_le (fun x hx => by
      change m x ≤ 1 / 2
      linarith only [hm x hx])
  have hg : eVariationOn (fun x => n x * l x * (1 / (1 - m x))) s ≤
      4 * eVariationOn m s + 2 * (eVariationOn l s + eVariationOn n s) := by
    have hb := eVariationOn_fun_mul_le hprodN hiN
    simp only [one_mul] at hb
    exact hb.trans (add_le_add hi (mul_le_mul' le_rfl hp))
  have hc : eVariationOn (fun _ : ℝ => (-4 : ℝ)) s = 0 :=
    eVariationOn.constant_on (by
      rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
      rfl)
  have hscale := eVariationOn_fun_mul_le (s := s)
    (f := fun _ : ℝ => (-4 : ℝ))
    (g := fun x => n x * l x * (1 / (1 - m x))) (C := 4) (D := ⊤)
    (by intro x hx; rw [← ofReal_norm]; norm_num) (by intro x hx; exact le_top)
  rw [hc, mul_zero, add_zero] at hscale
  have heq : (fun x => -4 * n x * l x / (1 - m x)) =
      (fun x => (-4 : ℝ) * (n x * l x * (1 / (1 - m x)))) := by
    funext x
    ring
  rw [heq]
  exact (hscale.trans (mul_le_mul' le_rfl hg)).trans_eq (by ring)

private theorem four_variations_le {s : Set ℝ} {l n m : ℝ → ℝ} {B : ℝ}
    (_hB : 0 ≤ B) (hl : ∀ x ∈ s, 0 ≤ l x ∧ l x ≤ 1)
    (hn : ∀ x ∈ s, 0 ≤ -n x ∧ -n x ≤ 1) (hm : ∀ x ∈ s, 1 / 2 ≤ 1 - m x)
    (hVl : eVariationOn l s ≤ ENNReal.ofReal B)
    (hVn : eVariationOn n s ≤ ENNReal.ofReal B)
    (hVm : eVariationOn m s ≤ ENNReal.ofReal B) :
    eVariationOn l s + eVariationOn n s + eVariationOn m s +
      eVariationOn (fun x => -4 * n x * l x / (1 - m x)) s ≤ ENNReal.ofReal (35 * B) := by
  apply (add_le_add (add_le_add (add_le_add hVl hVn) hVm) (metric_variation_le hl hn hm)).trans
  calc
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B + ENNReal.ofReal B +
        (8 * (ENNReal.ofReal B + ENNReal.ofReal B) + 16 * ENNReal.ofReal B) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 35)]; norm_num; ring

/-- [node restart-bv-geometry-TV]
On each complete outgoing or incoming section, the sum of the variations
of `λ`, `ν`, `μ`, and the literal `Ω²` is at most `C ε²`. Positive thresholds
and `C` precede every datum and depend only on the fixed box, uniformly in
higher initial derivatives. Both families are included explicitly. -/
theorem bv_geometry_tv : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∀ u ∈ Icc 0 T,
        eVariationOn (S.lam u) (Icc u T) + eVariationOn (S.nu u) (Icc u T) +
          eVariationOn (S.mu u) (Icc u T) + eVariationOn (S.Omega2 u) (Icc u T) ≤
            ENNReal.ofReal (C * ε ^ 2)) ∧
      (∀ v ∈ Icc 0 T,
        eVariationOn (fun u => S.lam u v) (Icc 0 v) +
          eVariationOn (fun u => S.nu u v) (Icc 0 v) +
          eVariationOn (fun u => S.mu u v) (Icc 0 v) +
          eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤ ENNReal.ofReal (C * ε ^ 2)) := by
  obtain ⟨ε₁, δ₁, Cs, hε₁, hδ₁, hCs, hsame⟩ := same_direction_expansion_variation
  obtain ⟨ε₂, δ₂, Cx, hε₂, hδ₂, hCx, hcross⟩ := cross_expansion_variation
  obtain ⟨ε₃, δ₃, Cm, hε₃, hδ₃, hCm, hmass⟩ := mass_characteristic_variation
  refine ⟨min ε₁ (min ε₂ ε₃), min δ₁ (min δ₂ δ₃), 35 * (Cs + Cx + Cm),
    lt_min hε₁ (lt_min hε₂ hε₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), by positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have he1 := hε.trans (min_le_left _ _)
  have he2 := (hε.trans (min_le_right _ _)).trans (min_le_left _ _)
  have he3 := (hε.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hd1 := hδ.trans (min_le_left _ _)
  have hd2 := (hδ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hd3 := (hδ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hb (D : ℝ) (hD : D ≤ Cs + Cx + Cm) :
      ENNReal.ofReal (D * ε ^ 2) ≤ ENNReal.ofReal ((Cs + Cx + Cm) * ε ^ 2) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hD (sq_nonneg ε))
  have bs := hb Cs (by linarith only [hCx, hCm])
  have bx := hb Cx (by linarith only [hCs, hCm])
  have bm := hb Cm (by linarith only [hCs, hCx])
  constructor
  · intro u hu
    have po (x : ℝ) (hx : x ∈ Icc u T) : (u, x) ∈ triangle 0 T := ⟨hu.1, hx.1, hx.2⟩
    have hb := four_variations_le (s := Icc u T)
      (show 0 ≤ (Cs + Cx + Cm) * ε ^ 2 by positivity)
      (fun x hx => ⟨(hset.c1.lam_pos (u, x) (po x hx)).le, (hset.box (u, x) (po x hx)).2.1⟩)
      (fun x hx => ⟨(neg_pos.mpr (hset.c1.nu_neg (u, x) (po x hx))).le,
        (hset.box (u, x) (po x hx)).2.2.2.1⟩)
      (fun x hx => (hset.box (u, x) (po x hx)).2.2.2.2.1)
      ((hsame e T ε M S h hset he1 hd1 u T hu.1 hu.2 le_rfl).1.trans bs)
      ((hcross e T ε M S h hset he2 hd2 u T hu.1 hu.2 le_rfl).1.trans bx)
      ((hmass e T ε M S h hset he3 hd3 u T hu.1 hu.2 le_rfl).1.2.trans bm)
    have heq : (fun x => -4 * S.nu u x * S.lam u x / (1 - S.mu u x)) = S.Omega2 u := rfl
    rw [heq] at hb
    simpa only [mul_assoc] using hb
  · intro v hv
    have pi (x : ℝ) (hx : x ∈ Icc 0 v) : (x, v) ∈ triangle 0 T := ⟨hx.1, hx.2, hv.2⟩
    have hb := four_variations_le (s := Icc 0 v)
      (show 0 ≤ (Cs + Cx + Cm) * ε ^ 2 by positivity)
      (fun x hx => ⟨(hset.c1.lam_pos (x, v) (pi x hx)).le, (hset.box (x, v) (pi x hx)).2.1⟩)
      (fun x hx => ⟨(neg_pos.mpr (hset.c1.nu_neg (x, v) (pi x hx))).le,
        (hset.box (x, v) (pi x hx)).2.2.2.1⟩)
      (fun x hx => (hset.box (x, v) (pi x hx)).2.2.2.2.1)
      ((hcross e T ε M S h hset he2 hd2 0 v le_rfl hv.1 hv.2).2.trans bx)
      ((hsame e T ε M S h hset he1 hd1 0 v le_rfl hv.1 hv.2).2.trans bs)
      ((hmass e T ε M S h hset he3 hd3 0 v le_rfl hv.1 hv.2).2.2.trans bm)
    have heq : (fun x => -4 * S.nu x v * S.lam x v / (1 - S.mu x v)) =
        (fun x => S.Omega2 x v) := rfl
    rw [heq] at hb
    simpa only [mul_assoc] using hb

end EmcsfAcExtension.Local
