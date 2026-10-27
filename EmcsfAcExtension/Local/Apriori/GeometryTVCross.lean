module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.GeometryTVAux
import EmcsfAcExtension.Local.Apriori.GeometryBoxMass
import EmcsfAcExtension.Local.Apriori.GeometryBoxFlux
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Cross characteristic expansion variations

The radius equation is integrated with the corresponding weighted mass
budget in each orientation (`charged_SF_new_version.tex:L4897–L4898`).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem cross_speed_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
    |S.rUV u v| ≤ 2 * (S.lam u v / S.r u v * S.mu u v) +
        8 * e ^ 2 * M ^ 2 * ε ^ 2 * (S.lam u v * S.r u v) ∧
    |S.rUV u v| ≤ 2 * (-S.nu u v / S.r u v * S.mu u v) +
        8 * e ^ 2 * M ^ 2 * ε ^ 2 * ((-S.nu u v) * S.r u v) := by
  have hr := hset.c1.r_pos (u, v) hp huv
  have hn := hset.c1.nu_neg (u, v) hp
  have hl := hset.c1.lam_pos (u, v) hp
  have hH := hset.c1.one_sub_mu_pos (u, v) hp
  have hmu := hset.mu_nonneg hp
  have hq0 : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hd : |S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| ≤
      S.mu u v + S.Q u v ^ 2 / S.r u v ^ 2 := by
    apply abs_le.mpr
    constructor <;> linarith only [hmu, hq0]
  have hq := hset.charge_sq_div_le hp
  have hco : (-S.nu u v) / (1 - S.mu u v) ≤ 2 := by
    apply (div_le_iff₀ hH).mpr
    linarith only [(hset.box (u, v) hp).2.2.2.1, (hset.box (u, v) hp).2.2.2.2.1]
  have hci : S.lam u v / (1 - S.mu u v) ≤ 2 := by
    apply (div_le_iff₀ hH).mpr
    linarith only [(hset.box (u, v) hp).2.1, (hset.box (u, v) hp).2.2.2.2.1]
  have heq : |S.rUV u v| = (-S.nu u v) * S.lam u v / S.r u v *
      (|S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| / (1 - S.mu u v)) := by
    simp only [Fields.rUV, abs_mul, abs_div, abs_of_neg hn, abs_of_pos hl,
      abs_of_pos hr, abs_of_pos hH]
  have hout : |S.rUV u v| ≤ 2 * (S.lam u v / S.r u v) *
      (S.mu u v + 4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) := by
    rw [heq]
    calc
      _ = ((-S.nu u v) / (1 - S.mu u v)) * (S.lam u v / S.r u v) *
          |S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hco (div_nonneg hl.le hr.le))
        (hd.trans (add_le_add le_rfl hq)) (abs_nonneg _)
        (mul_nonneg (by norm_num) (div_nonneg hl.le hr.le))
  have hin : |S.rUV u v| ≤ 2 * ((-S.nu u v) / S.r u v) *
      (S.mu u v + 4 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2) := by
    rw [heq]
    calc
      _ = (S.lam u v / (1 - S.mu u v)) * ((-S.nu u v) / S.r u v) *
          |S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hci (div_nonneg (neg_pos.mpr hn).le hr.le))
        (hd.trans (add_le_add le_rfl hq)) (abs_nonneg _)
        (mul_nonneg (by norm_num) (div_nonneg (neg_pos.mpr hn).le hr.le))
  constructor
  · convert hout using 1
    field_simp
    ring
  · convert hin using 1
    field_simp
    ring

/-- [node restart-sec-independent-area#cross-expansion-variation]
The outgoing variation of `ν` and incoming variation of `λ` on every
complete axis-to-point segment are at most `C ε²`. The positive thresholds
and `C` precede every datum and depend only on the fixed box, uniformly in
higher initial derivatives. The radius equation supplies both directions. -/
theorem cross_expansion_variation : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      eVariationOn (S.nu u) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2) ∧
      eVariationOn (fun x => S.lam x v) (Icc u v) ≤ ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨ε₀, δ₁, hε₀, hδ₁, hflux⟩ := closed_quadratic_scalar_budgets
  refine ⟨ε₀, min δ₁ 1, 80, hε₀, lt_min hδ₁ (by norm_num), by norm_num, ?_⟩
  intro e T ε M S h hset hε hδ u v hu huv hvT
  have hmass := hset.weighted_mass_preclosure hu huv hvT
  have hf := hflux e T ε M S h hset hε (hδ.trans (min_le_left _ _)) u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  have hr0 := hset.radius_nonneg hp
  have hrT : S.r u v ≤ T := (Area.radius_bounds hset hu huv hvT).2.trans
    (by linarith only [hu, hvT])
  have hd0 : 0 ≤ |e| * (T / 2) * M := by have := hset.pos; have := hset.one_le_M; positivity
  have hd2 : (|e| * (T / 2) * M) ^ 2 ≤ 1 := by
    nlinarith only [hd0, hδ.trans (min_le_right δ₁ 1)]
  have hE : 8 * e ^ 2 * M ^ 2 * ε ^ 2 * S.r u v ^ 2 ≤ 32 * ε ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2)
      (show 0 ≤ 8 * e ^ 2 * M ^ 2 * ε ^ 2 by positivity)
    have hj := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ 32 * ε ^ 2 by positivity)
    simp only [mul_pow, sq_abs] at hj
    nlinarith only [hi, hj]
  have hS := hset.c1.toIsSolution hset.pos
  have ho : outSeg u u v ⊆ triangle 0 T := by
    rintro p ⟨rfl, hx⟩; exact ⟨hu, hx.1, hx.2.trans hvT⟩
  have hi : inSeg u v v ⊆ triangle 0 T := by
    rintro p ⟨hx, hy, rfl⟩; exact ⟨hu.trans hx, hy, hvT⟩
  have po (x : ℝ) (hx : x ∈ Icc u v) : (u, x) ∈ triangle 0 T := ho ⟨rfl, hx⟩
  have pi (x : ℝ) (hx : x ∈ Icc u v) : (x, v) ∈ triangle 0 T := hi ⟨hx.1, hx.2, rfl⟩
  constructor
  · have cn : ContinuousOn (S.nu u) (Icc u v) := continuousOn_out_section hS.cont_nu ho
    have cg : ContinuousOn (pdV (triangle 0 T) S.nu u) (Icc u v) :=
      (continuousOn_pdV hset.c1.c1_nu (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_const.prodMk continuous_id).continuousOn (po · ·)
    have iw : IntervalIntegrable (fun x => S.lam u x * S.r u x) volume u v :=
      ((continuousOn_out_section hS.cont_lam ho).mul
        (continuousOn_out_section hS.cont_r ho)).intervalIntegrable_of_Icc huv
    let B := fun x => 2 * (S.lam u x / S.r u x * S.mu u x) +
      (8 * e ^ 2 * M ^ 2 * ε ^ 2) * (S.lam u x * S.r u x)
    have ib : IntervalIntegrable B volume u v :=
      (hmass.1.1.const_mul 2).add (iw.const_mul _)
    have hb := (ac_and_variation_le_of_interior_speed huv cn (cg.mono Ioo_subset_Icc_self)
      (fun x hx => (hasDerivWithinAt_pdV hset.c1.c1_nu
        (po x ⟨hx.1.le, hx.2.le⟩) (po · ·)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      ib (fun x hx => by
        rw [(hset.c1.eq_v (u, x) (po x ⟨hx.1.le, hx.2.le⟩) hx.1).2.1]
        exact (cross_speed_bound hset (po x ⟨hx.1.le, hx.2.le⟩) hx.1).1)).2
    apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [intervalIntegral.integral_add (hmass.1.1.const_mul 2) (iw.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hm := outgoing_radius_moment hS huv ho 1
    norm_num only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
    rw [hm]
    nlinarith only [hmass.1.2, hf.1, hE, sq_nonneg ε]
  · have cl : ContinuousOn (fun x => S.lam x v) (Icc u v) := continuousOn_in_section hS.cont_lam hi
    have cg : ContinuousOn (fun x => pdU (triangle 0 T) S.lam x v) (Icc u v) :=
      (continuousOn_pdU hset.c1.c1_lam (uniqueDiffOn_triangle hset.pos)).comp
        (continuous_id.prodMk continuous_const).continuousOn (pi · ·)
    have iw : IntervalIntegrable (fun x => (-S.nu x v) * S.r x v) volume u v :=
      ((continuousOn_in_section hS.cont_nu hi).neg.mul
        (continuousOn_in_section hS.cont_r hi)).intervalIntegrable_of_Icc huv
    let B := fun x => 2 * (-S.nu x v / S.r x v * S.mu x v) +
      (8 * e ^ 2 * M ^ 2 * ε ^ 2) * ((-S.nu x v) * S.r x v)
    have ib : IntervalIntegrable B volume u v :=
      (hmass.2.1.const_mul 2).add (iw.const_mul _)
    have hb := (ac_and_variation_le_of_interior_speed huv cl (cg.mono Ioo_subset_Icc_self)
      (fun x hx => (hasDerivWithinAt_pdU hset.c1.c1_lam
        (pi x ⟨hx.1.le, hx.2.le⟩) (pi · ·)).hasDerivAt (Icc_mem_nhds hx.1 hx.2))
      ib (fun x hx => by
        rw [(hset.c1.eq_u (x, v) (pi x ⟨hx.1.le, hx.2.le⟩) hx.2).2.1]
        exact (cross_speed_bound hset (pi x ⟨hx.1.le, hx.2.le⟩) hx.2).2)).2
    apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [intervalIntegral.integral_add (hmass.2.1.const_mul 2) (iw.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hm := incoming_radius_moment_of_solution hS huv hi 1
    norm_num only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
    rw [hm]
    nlinarith only [hmass.2.2, hf.2, hE, sq_nonneg ε]

end EmcsfAcExtension.Local
