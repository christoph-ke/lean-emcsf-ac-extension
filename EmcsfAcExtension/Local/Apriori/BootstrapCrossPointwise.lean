module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Potential
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Cross partials of the normalized scalar fields

The cross transports contain the cross expansion derivative multiplied by
a small scalar ratio, and electric terms of size `e² M² ε r`. Thus the
ordinary opposite-family variations require no higher initial derivative.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

private theorem cross_partial_identities {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    pdU (triangle 0 T) S.a u v = -(I * e * S.A u v * S.a u v) -
      ((S.rUV u v / S.lam u v : ℝ) : ℂ) * (S.theta u v / S.lam u v) +
      (-(S.nu u v : ℂ) / S.r u v) *
        (I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) ∧
    pdV (triangle 0 T) S.b u v =
      -((S.rUV u v / S.nu u v : ℝ) : ℂ) * (S.xi u v / S.nu u v) +
      ((S.lam u v : ℂ) / S.r u v) *
        (I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hrC := Complex.ofReal_ne_zero.mpr (hS.r_pos (u, v) hp huv).ne'
  have hlC := Complex.ofReal_ne_zero.mpr (hS.lam_pos (u, v) hp).ne'
  have hnC := Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, v) hp).ne
  have hHC := Complex.ofReal_ne_zero.mpr (hS.one_sub_mu_pos (u, v) hp).ne'
  have hH : (1 : ℂ) - S.mu u v ≠ 0 := by exact_mod_cast (hS.one_sub_mu_pos (u, v) hp).ne'
  constructor
  · have hd := ((hasDerivWithinAt_u_aux hS.c1_a hu huv.le hvT).derivWithin
      (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩)).symm.trans
      ((eq_normalized_in hS hu huv hvT).derivWithin
        (uniqueDiffOn_Icc (hu.trans_lt huv) u ⟨hu, huv.le⟩))
    rw [hd]
    dsimp only [Fields.rUV]
    push_cast
    field_simp [hrC, hlC, hHC, hH]
    ring
  · have hd := ((hasDerivWithinAt_v_aux hS.c1_b hu huv.le hvT).derivWithin
      (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩)).symm.trans
      ((eq_normalized_out hS hu huv hvT).derivWithin
        (uniqueDiffOn_Icc (huv.trans_le hvT) v ⟨huv.le, hvT⟩))
    rw [hd]
    dsimp only [Fields.rUV]
    push_cast
    field_simp [hrC, hnC, hHC, hH]
    ring

private theorem charged_drift_bound {w r H e Q M ε : ℝ} {φ : ℂ}
    (hr : 0 < r) (hH : 1 / 2 ≤ H) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hw : |w| ≤ 1) (hQ : |Q| ≤ 2 * |e| * M * ε * r ^ 2) (hφ : ‖φ‖ ≤ M) :
    ‖((w : ℂ) / r) * (I * e * Q * φ / H)‖ ≤ 4 * e ^ 2 * M ^ 2 * ε * r := by
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num) hH
  simp only [norm_mul, norm_div, norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hHp]
  calc
    _ ≤ 1 / r * (|e| * (2 * |e| * M * ε * r ^ 2) * M / (1 / 2)) := by gcongr
    _ = _ := by field_simp; rw [sq_abs]; ring

private theorem ratio_cross_term {d l ε : ℝ} {x : ℂ}
    (hl : 1 / 4 ≤ |l|) (_hε : 0 ≤ ε) (hx : ‖x‖ ≤ 4 * ε) :
    ‖((d / l : ℝ) : ℂ) * x‖ ≤ 16 * ε * |d| := by
  have hlp : 0 < |l| := lt_of_lt_of_le (by norm_num) hl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div]
  calc
    _ ≤ |d| / (1 / 4) * (4 * ε) := by gcongr
    _ = _ := by ring

/-- The normalized scalar cross partials are bounded by the cross expansion
partials times `16 ε`, plus a universal electric coefficient times
`e² M² ε r`. The coefficient is chosen before all data, depends only on the
box, and is uniform in higher derivatives. Both ordinary partials are used. -/
theorem normalized_cross_partial_bounds : ∃ Ce : ℝ, 0 < Ce ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ∀ u v, (u, v) ∈ triangle 0 T → u < v →
      ‖pdU (triangle 0 T) S.a u v‖ ≤ 16 * ε * |pdU (triangle 0 T) S.lam u v| +
        Ce * e ^ 2 * M ^ 2 * ε * S.r u v ∧
      ‖pdV (triangle 0 T) S.b u v‖ ≤ 16 * ε * |pdV (triangle 0 T) S.nu u v| +
        Ce * e ^ 2 * M ^ 2 * ε * S.r u v := by
  obtain ⟨Ca, hCa, hpotential⟩ := axis_gauge_potential_bound
  refine ⟨4 + 2 * Ca, by positivity, ?_⟩
  intro e T ε M S h hset u v hp huv
  have he := hset.eps_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have hr := hset.c1.r_pos (u, v) hp huv
  have hn := hset.c1.nu_neg (u, v) hp
  have hl := hset.c1.lam_pos (u, v) hp
  have hb := hset.box (u, v) hp
  have h4ε : 4 * ε ≤ M := by rw [hset.M_eq]; have := norm_nonneg (h 0); linarith
  have ha : ‖S.a u v‖ ≤ 2 * M := by
    rw [Fields.a]
    have hi := (norm_add_le _ _).trans (add_le_add hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1)
    linarith only [hi, h4ε]
  have hA := (hpotential e T ε M S h hset u v hp).2
  have hg : ‖I * e * S.A u v * S.a u v‖ ≤
      2 * Ca * e ^ 2 * M ^ 2 * ε * S.r u v := by
    simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |e| * (Ca * |e| * M * ε * S.r u v) * (2 * M) := by gcongr
      _ = _ := by rw [← sq_abs]; ring
  have hcharge := hset.charge_le hp
  have hφ := hb.2.2.2.2.2.1
  have hco : |-S.nu u v| ≤ 1 := by simpa only [abs_neg, abs_of_neg hn] using hb.2.2.2.1
  have hci : |S.lam u v| ≤ 1 := by simpa only [abs_of_pos hl] using hb.2.1
  have hdi := charged_drift_bound hr hb.2.2.2.2.1 hM he hco hcharge hφ
  have hdo := charged_drift_bound hr hb.2.2.2.2.1 hM he hci hcharge hφ
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at hdi hdo
  have hlo : 1 / 4 ≤ |S.lam u v| := by simpa only [abs_of_pos hl] using hb.1
  have hni : 1 / 4 ≤ |S.nu u v| := by simpa only [abs_of_neg hn] using hb.2.2.1
  have hto := ratio_cross_term (d := S.rUV u v) hlo he hb.2.2.2.2.2.2.1
  have hti := ratio_cross_term (d := S.rUV u v) hni he hb.2.2.2.2.2.2.2
  have hi := cross_partial_identities hset.c1 hp.1 huv hp.2.2
  have hlam := (hset.c1.eq_u (u, v) hp huv).2.1
  have hnu := (hset.c1.eq_v (u, v) hp huv).2.1
  constructor
  · rw [hi.1, hlam]
    have ht := (norm_add_le (-(I * e * S.A u v * S.a u v) -
      ((S.rUV u v / S.lam u v : ℝ) : ℂ) * (S.theta u v / S.lam u v))
      ((-(S.nu u v : ℂ) / S.r u v) *
        (I * e * S.Q u v * S.phi u v / (1 - S.mu u v)))).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    simp only [norm_neg, Complex.ofReal_neg] at ht hdi
    linarith only [ht, hg, hto, hdi]
  · rw [hi.2, hnu]
    have ht := norm_add_le (-((S.rUV u v / S.nu u v : ℝ) : ℂ) *
      (S.xi u v / S.nu u v)) (((S.lam u v : ℂ) / S.r u v) *
        (I * e * S.Q u v * S.phi u v / (1 - S.mu u v)))
    simp only [neg_mul, norm_neg] at ht ⊢
    have helectric : 0 ≤ 2 * Ca * e ^ 2 * M ^ 2 * ε * S.r u v := by positivity
    linarith only [ht, hti, hdo, helectric]

end EmcsfAcExtension.Local
