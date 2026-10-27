module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseEndpoint
import EmcsfAcExtension.Local.Apriori.AreaTransport
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.TransportJ
import EmcsfAcExtension.Local.Calculus.TransportK
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Characteristic modulus estimates for the classical fields

The ordinary transport retains the imaginary connection. Only its real
coefficient contributes to amplification. Endpoint passage uses continuity
of the canonical classical derivatives, as in `charged_SF_new_version.tex:L4734–L4767`.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem transport_terms_continuous {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    let D := triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}
    ContinuousOn (fun p : ℝ × ℝ => -(I * e * S.A p.1 p.2) +
      ((-‖S.xi p.1 p.2‖ ^ 2 / (S.nu p.1 p.2 * S.r p.1 p.2) : ℝ) : ℂ)) D ∧
    ContinuousOn (fun p : ℝ × ℝ =>
      ((-‖S.theta p.1 p.2‖ ^ 2 / (S.lam p.1 p.2 * S.r p.1 p.2) : ℝ) : ℂ)) D ∧
    ContinuousOn (fun p : ℝ × ℝ =>
      S.nu p.1 p.2 * S.theta p.1 p.2 / S.r p.1 p.2 ^ 2 *
        (curv S p.1 p.2 + 2 * starRingEnd ℂ (curv S p.1 p.2)) +
          emSourceJ e S p.1 p.2) D ∧
    ContinuousOn (fun p : ℝ × ℝ =>
      S.lam p.1 p.2 * S.xi p.1 p.2 / S.r p.1 p.2 ^ 2 *
        (starRingEnd ℂ (curv S p.1 p.2) + 2 * curv S p.1 p.2) +
          emSourceK e S p.1 p.2) D := by
  let D := triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := hS.c1_r.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cn := hS.c1_nu.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cl := hS.c1_lam.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cq := hS.c1_Q.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cp := hS.c1_phi.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have ca := hS.c1_A.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have ct := hS.c1_theta.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cx := hS.c1_xi.continuousOn.mono (show D ⊆ triangle 0 s from inter_subset_left)
  have cc := (continuousOn_curv_aux hs hS).mono
    (show D ⊆ triangle 0 s from inter_subset_left)
  have hr (p : ℝ × ℝ) (hp : p ∈ D) : S.r p.1 p.2 ≠ 0 :=
    (hS.r_pos p hp.1 hp.2).ne'
  have hn (p : ℝ × ℝ) (hp : p ∈ D) : S.nu p.1 p.2 ≠ 0 :=
    (hS.nu_neg p hp.1).ne
  have hl (p : ℝ × ℝ) (hp : p ∈ D) : S.lam p.1 p.2 ≠ 0 :=
    (hS.lam_pos p hp.1).ne'
  have hrC (p : ℝ × ℝ) (hp : p ∈ D) : (S.r p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hr p hp)
  have hnC (p : ℝ × ℝ) (hp : p ∈ D) : (S.nu p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hn p hp)
  have hlC (p : ℝ × ℝ) (hp : p ∈ D) : (S.lam p.1 p.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hl p hp)
  have crc := Complex.continuous_ofReal.comp_continuousOn cr
  have cnc := Complex.continuous_ofReal.comp_continuousOn cn
  have clc := Complex.continuous_ofReal.comp_continuousOn cl
  have cqc := Complex.continuous_ofReal.comp_continuousOn cq
  have cac := Complex.continuous_ofReal.comp_continuousOn ca
  have hrr (p : ℝ × ℝ) (hp : p ∈ D) : (S.r p.1 p.2 : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (hrC p hp)
  have cy := ct.div clc hlC
  have cz := cx.div cnc hnC
  have ce := (cqc.pow 2).div (crc.pow 2) hrr
  have cQv : ContinuousOn (fun p : ℝ × ℝ => (S.QV e p.1 p.2 : ℂ)) D := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact ((continuousOn_const.mul cr).mul
      (Complex.continuous_im.comp_continuousOn (cp.star.mul ct))).neg
  have cQu : ContinuousOn (fun p : ℝ × ℝ => (S.QU e p.1 p.2 : ℂ)) D := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact (continuousOn_const.mul cr).mul
      (Complex.continuous_im.comp_continuousOn (cp.star.mul cx))
  have cjlead := (cnc.neg.mul clc).div (crc.pow 2) hrr
  change ContinuousOn _ D ∧ ContinuousOn _ D ∧ ContinuousOn _ D ∧ ContinuousOn _ D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((continuousOn_const.mul cac).neg).add
      (Complex.continuous_ofReal.comp_continuousOn
        ((cx.norm.pow 2).neg.div (cn.mul cr) (fun p hp =>
          mul_ne_zero (hn p hp) (hr p hp))))
  · exact Complex.continuous_ofReal.comp_continuousOn
      ((ct.norm.pow 2).neg.div (cl.mul cr) (fun p hp =>
        mul_ne_zero (hl p hp) (hr p hp)))
  · exact (((cnc.mul ct).div (crc.pow 2) hrr).mul
      (cc.add (continuousOn_const.mul cc.star))).add
        ((cjlead.mul (((continuousOn_const.mul ce).mul cy).add
          ((continuousOn_const.mul cqc).mul ((continuousOn_const.mul cy).add cp)))).add
            (((((continuousOn_const.mul cnc.neg).mul cQv).mul cp).div crc hrC)))
  · exact (((clc.mul cx).div (crc.pow 2) hrr).mul
      (cc.star.add (continuousOn_const.mul cc))).add
        ((cjlead.mul (((continuousOn_const.mul ce).mul cz).sub
          ((continuousOn_const.mul cqc).mul ((continuousOn_const.mul cz).add cp)))).add
            (((((continuousOn_const.mul clc).mul cQu).mul cp).div crc hrC)))

/-- A field continuous off the axis, and zero on the axis, has a measurable
norm after extension by zero from the triangle. No integrability or bound
on the rate of approach to the axis is required. -/
theorem measurable_triangle_enorm_of_zero_axis {s : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}))
    (hz : ∀ t ∈ Icc 0 s, f (t, t) = 0) :
    Measurable ((triangle 0 s).indicator (fun p => ‖f p‖ₑ)) := by
  classical
  have hD : MeasurableSet (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
    (measurableSet_triangle 0 s).inter (measurableSet_lt measurable_fst measurable_snd)
  have hm := hf.enorm.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hD
  convert hm using 1
  funext p
  by_cases hp : p ∈ triangle 0 s
  · rw [indicator_of_mem hp]
    by_cases hlt : p.1 < p.2
    · rw [piecewise_eq_of_mem _ _ _
        (show p ∈ triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}
        from ⟨hp, hlt⟩)]
    · have heq : p.1 = p.2 := le_antisymm hp.2.1 (not_lt.mp hlt)
      rw [piecewise_eq_of_notMem _ _ _
        (show p ∉ triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}
        from fun h => hlt h.2)]
      have hpd : p = (p.1, p.1) := Prod.ext rfl heq.symm
      rw [hpd, hz p.1 ⟨hp.1, heq.le.trans hp.2.2⟩, enorm_zero]
  · rw [indicator_of_notMem hp, piecewise_eq_of_notMem _ _ _ (show
      p ∉ triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2} from fun h => hp h.1)]

/-- The norms of both characteristic forcing fields, extended by zero from
the triangle, are measurable. This is an analytic statement with no estimate
constant or assumed integrability at the axis. -/
theorem measurable_transport_forcing {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    Measurable ((triangle 0 s).indicator (fun p : ℝ × ℝ =>
      ‖S.nu p.1 p.2 * S.theta p.1 p.2 / S.r p.1 p.2 ^ 2 *
        (curv S p.1 p.2 + 2 * starRingEnd ℂ (curv S p.1 p.2)) +
          emSourceJ e S p.1 p.2‖ₑ)) ∧
    Measurable ((triangle 0 s).indicator (fun p : ℝ × ℝ =>
      ‖S.lam p.1 p.2 * S.xi p.1 p.2 / S.r p.1 p.2 ^ 2 *
        (starRingEnd ℂ (curv S p.1 p.2) + 2 * curv S p.1 p.2) +
          emSourceK e S p.1 p.2‖ₑ)) := by
  have ht := transport_terms_continuous hs hS
  constructor
  · apply measurable_triangle_enorm_of_zero_axis ht.2.2.1
    intro t ht
    simp only [emSourceJ, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1,
      Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul,
      mul_zero, add_zero]
  · apply measurable_triangle_enorm_of_zero_axis ht.2.2.2
    intro t ht
    simp only [emSourceK, (hS.axis t ⟨ht.1, le_rfl, ht.2⟩).1,
      Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), div_zero, zero_mul,
      mul_zero, add_zero]

/-- The outgoing renormalized derivative obeys its incoming characteristic
modulus estimate, including the axis endpoint. `C` depends only on the fixed
box and is independent of all data, parameters, and higher derivatives.
The forcing budget is kept as an extended integral until the area estimate. -/
theorem j_characteristic_enorm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ s →
      ‖jC1 (triangle 0 s) S u v‖ₑ ≤
        ENNReal.ofReal (Real.exp (C * ε *
          ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal)) *
        (‖jC1 (triangle 0 s) S 0 v‖ₑ +
          ∫⁻ x in Icc 0 v,
            ‖S.nu x v * S.theta x v / S.r x v ^ 2 *
              (curv S x v + 2 * starRingEnd ℂ (curv S x v)) + emSourceJ e S x v‖ₑ) := by
  obtain ⟨C, hC, hhom⟩ := Area.homogeneous_transport_bounds
  refine ⟨C, hC, ?_⟩
  intro e s ε M S h hset hε u v hu huv hvs
  let H := Real.exp (C * ε *
    ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal)
  let g := fun x => jC1 (triangle 0 s) S x v
  let c := fun x => -(I * e * S.A x v) +
    ((-‖S.xi x v‖ ^ 2 / (S.nu x v * S.r x v) : ℝ) : ℂ)
  let q := fun x => S.nu x v * S.theta x v / S.r x v ^ 2 *
    (curv S x v + 2 * starRingEnd ℂ (curv S x v)) + emSourceJ e S x v
  have hH : 1 ≤ H := Real.one_le_exp (by
    have hi : 0 ≤ ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal :=
      intervalIntegral.integral_nonneg hset.pos.le (fun _ _ => ENNReal.toReal_nonneg)
    exact mul_nonneg (mul_nonneg hC.le hset.eps_nonneg) hi)
  rcases eq_or_lt_of_le hu with hu0 | hu0
  · subst u
    change ‖g 0‖ₑ ≤ ENNReal.ofReal H * (‖g 0‖ₑ + ∫⁻ x in Icc 0 v, ‖q x‖ₑ)
    calc
      _ ≤ ‖g 0‖ₑ + ∫⁻ x in Icc 0 v, ‖q x‖ₑ := le_add_right le_rfl
      _ ≤ _ := le_mul_of_one_le_left' (by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hH)
  · have hs : MapsTo (fun x => (x, v)) (Icc 0 u) (triangle 0 s) :=
      fun x hx => ⟨hx.1, hx.2.trans huv, hvs⟩
    have hso : MapsTo (fun x => (x, v)) (Ioo 0 u)
        (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
      fun x hx => ⟨⟨hx.1.le, hx.2.le.trans huv, hvs⟩, hx.2.trans_le huv⟩
    have cg : ContinuousOn g (Icc 0 u) :=
      (continuousOn_jC1_aux hset.pos hset.c1).comp (f := fun x : ℝ => (x, v))
        (continuous_id.prodMk continuous_const).continuousOn hs
    have terms := transport_terms_continuous hset.pos hset.c1
    have cc : ContinuousOn c (Ioo 0 u) := by
      exact terms.1.comp (f := fun x : ℝ => (x, v))
        (continuous_id.prodMk continuous_const).continuousOn hso
    have cq : ContinuousOn q (Ioo 0 u) := by
      exact terms.2.2.1.comp (f := fun x : ℝ => (x, v))
        (continuous_id.prodMk continuous_const).continuousOn hso
    have hd (x : ℝ) (hx : x ∈ Ioo 0 u) : HasDerivAt g (c x * g x + q x) x := by
      apply ((bv_j_trans hset.c1 hx.1.le (hx.2.trans_le huv) hvs).hasDerivAt
        (Icc_mem_nhds hx.1 (hx.2.trans_le huv))).congr_deriv
      dsimp only [c, g, q]
      push_cast
      ring
    have hp (d t : ℝ) (hd : 0 < d) (hdt : d ≤ t) (htu : t < u)
        (x : ℝ) (hx : x ∈ Icc d t) :
        Real.exp (∫ y in x..t, (c y).re) ≤ H := by
      have he : ∀ y, (c y).re = -‖S.xi y v‖ ^ 2 / (S.nu y v * S.r y v) := by
        intro y
        dsimp only [c]
        rw [Complex.add_re, Complex.neg_re]
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
          mul_zero, neg_zero, zero_add]
      simp_rw [he]
      exact (hhom e s ε M S h hset hε).1 v ⟨hu.trans huv, hvs⟩ x t
        (hd.le.trans hx.1) hx.2 (htu.le.trans huv)
    have hb := characteristic_transport_enorm_le_of_interior hu0
      ((by norm_num : (0 : ℝ) ≤ 1).trans hH) cg cc cq hd hp
    apply hb.trans
    apply mul_le_mul' le_rfl
    apply add_le_add le_rfl
    exact lintegral_mono_set (Icc_subset_Icc le_rfl huv)

/-- The incoming renormalized derivative is bounded by its axis value and
the outgoing forcing integral. The damping factor has coefficient exactly
one, uniformly in all solution parameters and derivative norms. No scalar
smallness is required for this characteristic estimate. -/
theorem k_characteristic_enorm_bound {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    ‖kC1 e (triangle 0 s) S u v‖ₑ ≤ ‖kC1 e (triangle 0 s) S u u‖ₑ +
      ∫⁻ x in Icc u s,
        ‖S.lam u x * S.xi u x / S.r u x ^ 2 *
          (starRingEnd ℂ (curv S u x) + 2 * curv S u x) + emSourceK e S u x‖ₑ := by
  let g := kC1 e (triangle 0 s) S u
  let c := fun x => ((-‖S.theta u x‖ ^ 2 / (S.lam u x * S.r u x) : ℝ) : ℂ)
  let q := fun x => S.lam u x * S.xi u x / S.r u x ^ 2 *
    (starRingEnd ℂ (curv S u x) + 2 * curv S u x) + emSourceK e S u x
  rcases eq_or_lt_of_le huv with huv0 | huv0
  · subst v
    exact le_add_right le_rfl
  · have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 s) :=
      fun x hx => ⟨hu, hx.1, hx.2.trans hvs⟩
    have hso : MapsTo (fun x => (u, x)) (Ioo u v)
        (triangle 0 s ∩ {p : ℝ × ℝ | p.1 < p.2}) :=
      fun x hx => ⟨⟨hu, hx.1.le, hx.2.le.trans hvs⟩, hx.1⟩
    have cg : ContinuousOn g (Icc u v) :=
      (continuousOn_kC1_aux hset.pos hset.c1).comp (f := fun x : ℝ => (u, x))
        (continuous_const.prodMk continuous_id).continuousOn hs
    have terms := transport_terms_continuous hset.pos hset.c1
    have cc : ContinuousOn c (Ioo u v) := by
      exact terms.2.1.comp (f := fun x : ℝ => (u, x))
        (continuous_const.prodMk continuous_id).continuousOn hso
    have cq : ContinuousOn q (Ioo u v) := by
      exact terms.2.2.2.comp (f := fun x : ℝ => (u, x))
        (continuous_const.prodMk continuous_id).continuousOn hso
    have hd (x : ℝ) (hx : x ∈ Ioo u v) : HasDerivAt g (c x * g x + q x) x := by
      apply ((bv_k_trans hset.c1 hu hx.1 (hx.2.le.trans hvs)).hasDerivAt
        (Icc_mem_nhds hx.1 (hx.2.trans_le hvs))).congr_deriv
      dsimp only [c, g, q]
      push_cast
      ring
    have hp (d t : ℝ) (hd : u < d) (hdt : d ≤ t) (htv : t < v)
        (x : ℝ) (hx : x ∈ Icc d t) : Real.exp (∫ y in x..t, (c y).re) ≤ 1 := by
      simp only [c, Complex.ofReal_re]
      exact Area.homogeneous_k_factor_le_one hset hu (hd.le.trans hx.1)
        hx.2 (htv.le.trans hvs)
    have hb := characteristic_transport_enorm_le_of_interior huv0
      (by norm_num : (0 : ℝ) ≤ 1) cg cc cq hd hp
    simp only [ENNReal.ofReal_one, one_mul] at hb
    apply hb.trans
    apply add_le_add le_rfl
    exact lintegral_mono_set (Icc_subset_Icc le_rfl hvs)

end EmcsfAcExtension.Local
