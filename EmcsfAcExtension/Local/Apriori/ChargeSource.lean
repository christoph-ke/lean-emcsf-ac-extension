module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Regular pointwise electromagnetic forcing

Absolute monomial estimates for `charged_SF_new_version.tex:L4649–L4653`.
The large constant scalar background remains explicit in the factor `M²`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem norm_em_bracket_le {e q r M ε : ℝ} {z p : ℂ}
    (hM : 1 ≤ M) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hq : |q| ≤ 2 * |e| * M * ε * r ^ 2)
    (hq2 : q ^ 2 / r ^ 2 ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 * r ^ 2)
    (hz : ‖z‖ ≤ 4 * ε) (hp : ‖p‖ ≤ M) (κ : ℂ) (hκ : ‖κ‖ = 1) :
    ‖5 * ((q ^ 2 / r ^ 2 : ℝ) : ℂ) * z + κ * e * q * (3 * z + p)‖ ≤
      106 * e ^ 2 * M ^ 2 * ε * r ^ 2 := by
  have heps2 : ε ^ 2 ≤ ε := by nlinarith only [hε0, hε]
  have hz4 : ‖z‖ ≤ 4 := hz.trans (by linarith only [hε])
  have hp3 : ‖3 * z + p‖ ≤ 13 * M := by
    calc
      _ ≤ ‖(3 : ℂ)‖ * ‖z‖ + ‖p‖ := (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ 3 * 4 + M := by norm_num; gcongr; linarith only [hz4]
      _ ≤ _ := by linarith only [hM]
  have hfirst : ‖5 * ((q ^ 2 / r ^ 2 : ℝ) : ℂ) * z‖ ≤
      80 * e ^ 2 * M ^ 2 * ε * r ^ 2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg q) (sq_nonneg r))]
    norm_num only [Complex.norm_ofNat]
    calc
      _ ≤ 5 * (4 * e ^ 2 * M ^ 2 * ε ^ 2 * r ^ 2) * 4 := by gcongr
      _ = (80 * e ^ 2 * M ^ 2 * r ^ 2) * ε ^ 2 := by ring
      _ ≤ (80 * e ^ 2 * M ^ 2 * r ^ 2) * ε := by gcongr
      _ = _ := by ring
  have hsecond : ‖κ * e * q * (3 * z + p)‖ ≤
      26 * e ^ 2 * M ^ 2 * ε * r ^ 2 := by
    simp only [norm_mul, hκ, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |e| * (2 * |e| * M * ε * r ^ 2) * (13 * M) := by gcongr
      _ = _ := by rw [← sq_abs e]; ring
  exact (norm_add_le _ _).trans (by linarith only [hfirst, hsecond])

private theorem norm_em_source_le {e q r M ε n l t d D : ℝ} {z p : ℂ}
    (hr : 0 < r) (hn : 0 ≤ n) (hl : 0 ≤ l) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (htd : t * d = n * l) (hM : 1 ≤ M) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hq : |q| ≤ 2 * |e| * M * ε * r ^ 2)
    (hq2 : q ^ 2 / r ^ 2 ≤ 4 * e ^ 2 * M ^ 2 * ε ^ 2 * r ^ 2)
    (hD : |D| ≤ 4 * |e| * M * ε * d * r)
    (hz : ‖z‖ ≤ 4 * ε) (hp : ‖p‖ ≤ M) (κ : ℂ) (hκ : ‖κ‖ = 1) :
    ‖((n * l / r ^ 2 : ℝ) : ℂ) *
        (5 * ((q ^ 2 / r ^ 2 : ℝ) : ℂ) * z + κ * e * q * (3 * z + p)) +
      I * e * t * D * p / r‖ ≤ 110 * e ^ 2 * M ^ 2 * ε * n * l := by
  have hb := norm_em_bracket_le hM hε0 hε hq hq2 hz hp κ hκ
  have hfirst : ‖((n * l / r ^ 2 : ℝ) : ℂ) *
      (5 * ((q ^ 2 / r ^ 2 : ℝ) : ℂ) * z + κ * e * q * (3 * z + p))‖ ≤
      106 * e ^ 2 * M ^ 2 * ε * n * l := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (mul_nonneg hn hl) (sq_nonneg r))]
    calc
      _ ≤ (n * l / r ^ 2) * (106 * e ^ 2 * M ^ 2 * ε * r ^ 2) := by gcongr
      _ = _ := by field_simp
  have hsecond : ‖I * e * t * D * p / r‖ ≤ 4 * e ^ 2 * M ^ 2 * ε * n * l := by
    simp only [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, abs_of_pos hr]
    calc
      _ ≤ |e| * t * (4 * |e| * M * ε * d * r) * M / r := by gcongr
      _ = (4 * e ^ 2 * M ^ 2 * ε) * (t * d) := by rw [← sq_abs e]; field_simp
      _ = _ := by rw [htd]; ring
  exact (norm_add_le _ _).trans (by linarith only [hfirst, hsecond])

/-- [node restart-bv-E-bounds]
Both regular electromagnetic sources (`charged_SF_new_version.tex:L4649–L4653`).
`C` is universal, independent of `e`, `s`, `M`, and all higher data norms.
The fixed threshold `ε ≤ 1` suffices; the charged length need not be small
for this pointwise estimate. -/
theorem bv_e_bounds : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 → ∀ u v, 0 ≤ u → u < v → v ≤ s →
      ‖emSourceJ e S u v‖ + ‖emSourceK e S u v‖ ≤
        C * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
  refine ⟨220, by norm_num, ?_⟩
  intro e s ε M S h hset hε u v hu huv hvs
  have hp : (u, v) ∈ triangle 0 s := ⟨hu, huv.le, hvs⟩
  have hr := hset.c1.r_pos (u, v) hp huv
  have hl := (hset.c1.lam_pos (u, v) hp).le
  have hn := (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le
  have hb := hset.box (u, v) hp
  have hQ := hset.charge_le hp
  have hQ2 := hset.charge_sq_div_le hp
  have hqv := hset.maxwell_v_le hp
  have hqu := hset.maxwell_u_le hp
  have hj := norm_em_source_le hr hn hl hn hl (by ring) hset.one_le_M hset.eps_nonneg hε
    hQ hQ2 hqv hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.1 I (by simp)
  have hk := norm_em_source_le hr hn hl hl hn (by ring) hset.one_le_M hset.eps_nonneg hε
    hQ hQ2 hqu hb.2.2.2.2.2.2.2 hb.2.2.2.2.2.1 (-I) (by simp)
  have hj' : ‖emSourceJ e S u v‖ ≤ 110 * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
    simpa only [emSourceJ, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg] using hj
  have hk' : ‖emSourceK e S u v‖ ≤ 110 * e ^ 2 * M ^ 2 * ε * (-S.nu u v) * S.lam u v := by
    simpa only [emSourceK, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using hk
  linarith only [hj', hk']

end EmcsfAcExtension.Local
