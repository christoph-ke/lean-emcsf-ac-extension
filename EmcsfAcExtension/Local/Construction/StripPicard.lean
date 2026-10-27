module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
import EmcsfAcExtension.Local.Broad.RectangleVolterra
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Continuous characteristic rectangles by weighted Picard iteration

The two source blocks are contracted simultaneously in an exponentially
weighted supremum norm. The construction uses the complete space of
continuous maps on the closed rectangle and requires no existence premise.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

private abbrev Rect (a b c d : ℝ) := Icc a b × Icc c d

private noncomputable def clampRect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (p : ℝ × ℝ) : Rect a b c d :=
  (projIcc a b hab p.1, projIcc c d hcd p.2)

private theorem continuous_clampRect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    Continuous (clampRect hab hcd) :=
  (continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd)

private noncomputable def rectWeight (a c k : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (k * (p.1 - a + (p.2 - c)))

private noncomputable def unweight {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (k : ℝ) (z : C(Rect a b c d, X × Y)) (p : ℝ × ℝ) : X × Y :=
  rectWeight a c k p • z (clampRect hab hcd p)

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem continuous_unweight {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (k : ℝ) (z : C(Rect a b c d, X × Y)) : Continuous (unweight hab hcd k z) := by
  have hw : Continuous (fun p : ℝ × ℝ => Real.exp (k*(p.1-a+(p.2-c)))) := by fun_prop
  exact hw.smul (z.continuous.comp (continuous_clampRect hab hcd))

private theorem continuous_variable_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℝ × ℝ → E) (hF : Continuous F) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ s in a..p.1, F (s, p.2)) := by
  have h : Continuous (fun q : (ℝ × ℝ) × ℝ => F ((q.1.1 - a) * q.2 + a, q.1.2)) :=
    hF.comp (by fun_prop)
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) (f := fun p : ℝ × ℝ => fun t : ℝ => F ((p.1-a)*t+a,p.2)) h
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have heq (p : ℝ × ℝ) : (∫ s in a..p.1, F (s, p.2)) =
      (p.1 - a) • ∫ t in Icc (0 : ℝ) 1, F ((p.1 - a) * t + a, p.2) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using (intervalIntegral.smul_integral_comp_mul_add
      (f := fun s => F (s, p.2)) (a := 0) (b := 1) (p.1 - a) a).symm
  simp_rw [heq]
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 - a)).smul hi

private noncomputable def rectanglePicard {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (k : ℝ) (fi : X × Y → X) (fo : X × Y → Y)
    (yi : ℝ → X) (xb : ℝ → Y) (hfi : Continuous fi) (hfo : Continuous fo)
    (hyi : Continuous yi) (hxb : Continuous xb)
    (z : C(Rect a b c d, X × Y)) : C(Rect a b c d, X × Y) := by
  let F := unweight hab hcd k z
  have hF := continuous_unweight hab hcd k z
  let G : ℝ × ℝ → X × Y := fun p =>
    (yi p.2 + ∫ s in a..p.1, fi (F (s,p.2)),
      xb p.1 + ∫ t in c..p.2, fo (F (p.1,t)))
  have hi := continuous_variable_integral (fi ∘ F) (hfi.comp hF) a
  have ho := (continuous_variable_integral
    (fun p : ℝ × ℝ => fo (F (p.2,p.1)))
    ((hfo.comp hF).comp continuous_swap) c).comp continuous_swap
  have hG : Continuous G := ((hyi.comp continuous_snd).add hi).prodMk
    ((hxb.comp continuous_fst).add ho)
  let r : Rect a b c d → ℝ × ℝ := fun p => (p.1,p.2)
  have hr : Continuous r := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hw : Continuous (fun p : ℝ × ℝ => Real.exp (k*(p.1-a+(p.2-c)))) := by fun_prop
  exact ⟨fun p => (rectWeight a c k (r p))⁻¹ • G (r p),
    ((hw.inv₀ (fun p => (Real.exp_pos _).ne')).smul hG).comp hr⟩

omit [CompleteSpace X] [CompleteSpace Y] in
private theorem norm_unweight_sub_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (k : ℝ) (z w : C(Rect a b c d, X × Y)) (p : ℝ × ℝ) :
    ‖unweight hab hcd k z p - unweight hab hcd k w p‖ ≤
      rectWeight a c k p * ‖z - w‖ := by
  dsimp only [unweight]
  rw [← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (show 0 < rectWeight a c k p from Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left ((z-w).norm_coe_le_norm _) (Real.exp_pos _).le

private theorem lipschitz_norm_sub_le {E Z : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup Z] {L : ℝ≥0} {f : E → Z} (hf : LipschitzWith L f)
    (x y : E) : ‖f x-f y‖ ≤ L*‖x-y‖ := by
  simpa only [dist_eq_norm] using hf.dist_le_mul x y

private theorem norm_rectanglePicard_sub_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {L : ℝ≥0} {k : ℝ} (hk : 0 < k) (fi : X × Y → X) (fo : X × Y → Y)
    (yi : ℝ → X) (xb : ℝ → Y) (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo)
    (hyi : Continuous yi) (hxb : Continuous xb)
    (z w : C(Rect a b c d, X × Y)) :
    ‖rectanglePicard hab hcd k fi fo yi xb hfi.continuous hfo.continuous hyi hxb z -
      rectanglePicard hab hcd k fi fo yi xb hfi.continuous hfo.continuous hyi hxb w‖ ≤
        (L / k) * ‖z - w‖ := by
  let Fz := unweight hab hcd k z
  let Fw := unweight hab hcd k w
  have hFz : Continuous Fz := continuous_unweight hab hcd k z
  have hFw : Continuous Fw := continuous_unweight hab hcd k w
  apply (ContinuousMap.norm_le _ (mul_nonneg (div_nonneg L.coe_nonneg hk.le) (norm_nonneg _))).mpr
  intro p
  let u : ℝ := p.1
  let v : ℝ := p.2
  have hi : ‖(∫ s in a..u, fi (Fz (s,v))) - ∫ s in a..u, fi (Fw (s,v))‖ ≤
      (L / k) * ‖z-w‖ * rectWeight a c k (u,v) := by
    rw [← intervalIntegral.integral_sub (f := fun s => fi (Fz (s,v))) (g := fun s => fi (Fw (s,v)))
      (((hfi.continuous.comp hFz).comp (show Continuous (fun s : ℝ => (s,v))
          by fun_prop)).intervalIntegrable (μ := volume) a u)
      (((hfi.continuous.comp hFw).comp (show Continuous (fun s : ℝ => (s,v))
          by fun_prop)).intervalIntegrable (μ := volume) a u)]
    apply Broad.norm_integral_le_exponential_of_bound p.1.property.1 hk L.coe_nonneg (norm_nonneg _)
    intro s _hs
    exact (lipschitz_norm_sub_le hfi _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_unweight_sub_le hab hcd k z w (s,v))
        L.coe_nonneg).trans_eq (by dsimp [rectWeight]; ring))
  have ho : ‖(∫ t in c..v, fo (Fz (u,t))) - ∫ t in c..v, fo (Fw (u,t))‖ ≤
      (L / k) * ‖z-w‖ * rectWeight a c k (u,v) := by
    rw [← intervalIntegral.integral_sub (f := fun t => fo (Fz (u,t))) (g := fun t => fo (Fw (u,t)))
      (((hfo.continuous.comp hFz).comp (show Continuous (fun t : ℝ => (u,t))
          by fun_prop)).intervalIntegrable (μ := volume) c v)
      (((hfo.continuous.comp hFw).comp (show Continuous (fun t : ℝ => (u,t))
          by fun_prop)).intervalIntegrable (μ := volume) c v)]
    have hb := Broad.norm_integral_le_exponential_of_bound p.2.property.1 hk L.coe_nonneg
      (norm_nonneg (z-w)) (y := u-a)
      (f := fun t => fo (Fz (u,t)) - fo (Fw (u,t))) (fun t _ht => by
        apply (lipschitz_norm_sub_le hfo _ _).trans
        apply (mul_le_mul_of_nonneg_left (norm_unweight_sub_le hab hcd k z w (u,t))
          L.coe_nonneg).trans_eq
        dsimp [rectWeight]
        rw [show u-a+(t-c)=t-c+(u-a) by ring]
        ring)
    change ‖∫ t in c..v, fo (Fz (u,t))-fo (Fw (u,t))‖ ≤
      (L/k)*‖z-w‖*Real.exp (k*(v-c+(u-a))) at hb
    simpa only [rectWeight,show v-c+(u-a)=u-a+(v-c) by ring] using hb
  change ‖(rectWeight a c k (u,v))⁻¹ •
      (yi v + ∫ s in a..u, fi (Fz (s,v)), xb u + ∫ t in c..v, fo (Fz (u,t))) -
    (rectWeight a c k (u,v))⁻¹ •
      (yi v + ∫ s in a..u, fi (Fw (s,v)), xb u + ∫ t in c..v, fo (Fw (u,t)))‖ ≤ _
  have hwp : 0 < rectWeight a c k (u,v) := Real.exp_pos _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwp)]
  have hpair : ‖(yi v + ∫ s in a..u, fi (Fz (s,v)), xb u + ∫ t in c..v, fo (Fz (u,t))) -
      (yi v + ∫ s in a..u, fi (Fw (s,v)), xb u + ∫ t in c..v, fo (Fw (u,t)))‖ ≤
      (L / k) * ‖z-w‖ * rectWeight a c k (u,v) := by
    simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, add_sub_add_left_eq_sub] using max_le hi
        ho
  refine (mul_le_mul_of_nonneg_left hpair (inv_pos.mpr hwp).le).trans_eq ?_
  calc
    _ = ((rectWeight a c k (u,v))⁻¹ * rectWeight a c k (u,v)) * ((L/k)*‖z-w‖) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hwp.ne',one_mul]

/-- Continuous Goursat existence for two globally Lipschitz characteristic
source blocks on any closed finite rectangle. The source coefficient is
fixed before the rectangle and boundary traces; no small side length is
required for this extended-source construction. -/
theorem continuous_rectangle_goursat {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {L : ℝ≥0} (fi : X × Y → X) (fo : X × Y → Y)
    (yi : ℝ → X) (xb : ℝ → Y) (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo)
    (hyi : Continuous yi) (hxb : Continuous xb) :
    ∃ F : ℝ × ℝ → X × Y, Continuous F ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        (F (u,v)).1 = yi v + ∫ s in a..u, fi (F (s,v))) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        (F (u,v)).2 = xb u + ∫ t in c..v, fo (F (u,t))) := by
  let k : ℝ := 2 * (L + 1)
  have hk : 0 < k := by dsimp [k]; positivity
  let T := rectanglePicard hab hcd k fi fo yi xb hfi.continuous hfo.continuous hyi hxb
  have hratio : (L : ℝ) / k ≤ 1/2 := by
    apply (div_le_iff₀ hk).mpr
    dsimp [k]
    linarith
  have hcontr : ContractingWith (1/2 : ℝ≥0) T := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun z w => ?_)⟩
    rw [dist_eq_norm, dist_eq_norm]
    exact (norm_rectanglePicard_sub_le hab hcd hk fi fo yi xb hfi hfo hyi hxb z w).trans
      (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))
  let z := ContractingWith.fixedPoint T hcontr
  have hz : T z = z := hcontr.fixedPoint_isFixedPt
  let F := unweight hab hcd k z
  have hfull u (hu : u ∈ Icc a b) v (hv : v ∈ Icc c d) :
      F (u,v) = (yi v + ∫ s in a..u, fi (F (s,v)),
        xb u + ∫ t in c..v, fo (F (u,t))) := by
    have hp := congrArg (fun w : C(Rect a b c d, X × Y) => w (⟨u,hu⟩,⟨v,hv⟩)) hz
    change (rectWeight a c k (u,v))⁻¹ •
      (yi v + ∫ s in a..u, fi (F (s,v)), xb u + ∫ t in c..v, fo (F (u,t))) =
        z (⟨u,hu⟩,⟨v,hv⟩) at hp
    have hmul := congrArg (fun q : X × Y => rectWeight a c k (u,v) • q) hp
    have hwp : 0 < rectWeight a c k (u,v) := Real.exp_pos _
    rw [smul_smul, mul_inv_cancel₀ hwp.ne', one_smul] at hmul
    have heval : F (u,v) = rectWeight a c k (u,v) • z (⟨u,hu⟩,⟨v,hv⟩) := by
      dsimp [F, unweight, clampRect]
      rw [projIcc_of_mem hab hu, projIcc_of_mem hcd hv]
    exact heval.trans hmul.symm
  exact ⟨F, continuous_unweight hab hcd k z,
    fun u hu v hv => congrArg Prod.fst (hfull u hu v hv),
    fun u hu v hv => congrArg Prod.snd (hfull u hu v hv)⟩

omit [CompleteSpace X] [CompleteSpace Y] in
/-- A reference residual controls a continuous Goursat solution in the
weighted supremum norm. `K,k` precede both functions; `k ≥ 2K` gives
coefficient two, uniformly in the rectangle and boundary traces. -/
theorem rectangle_goursat_distance_of_residual
    {a b c d K k ε : ℝ} {F G : ℝ × ℝ → X × Y}
    {fi : X × Y → X} {fo : X × Y → Y} {yi : ℝ → X} {xb : ℝ → Y}
    (hab : a ≤ b) (hcd : c ≤ d) (hK : 0 ≤ K) (hk : 0 < k)
    (hlarge : 2 * K ≤ k) (hε : 0 ≤ ε)
    (hF : Continuous F) (hG : Continuous G) (hfi : Continuous fi) (hfo : Continuous fo)
    (hFi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, fi (F (s, v)))
    (hFo : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = xb u + ∫ t in c..v, fo (F (u, t)))
    (hGi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      ‖yi v + (∫ s in a..u, fi (G (s, v))) - (G (u, v)).1‖ ≤ ε)
    (hGo : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      ‖xb u + (∫ t in c..v, fo (G (u, t))) - (G (u, v)).2‖ ≤ ε)
    (hLi : ∀ p ∈ Icc a b ×ˢ Icc c d, ‖fi (F p) - fi (G p)‖ ≤ K * ‖F p - G p‖)
    (hLo : ∀ p ∈ Icc a b ×ˢ Icc c d, ‖fo (F p) - fo (G p)‖ ≤ K * ‖F p - G p‖) :
    ∀ p ∈ Icc a b ×ˢ Icc c d,
      ‖F p-G p‖ ≤ 2*ε*Real.exp (k*(p.1-a+(p.2-c))) := by
  let w := fun p : ℝ × ℝ => Real.exp (-(k*(p.1-a+(p.2-c)))) * ‖F p-G p‖
  have hw : Continuous w := (by fun_prop : Continuous
    (fun p : ℝ × ℝ => Real.exp (-(k*(p.1-a+(p.2-c)))))).mul (hF.sub hG).norm
  obtain ⟨p₀,hp₀,hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(a,c), ⟨le_rfl,hab⟩,le_rfl,hcd⟩ hw.continuousOn
  let B := w p₀
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hbound p (hp : p ∈ Icc a b ×ˢ Icc c d) :
      ‖F p-G p‖ ≤ B*Real.exp (k*(p.1-a+(p.2-c))) := by
    have hm := hmax hp
    change Real.exp (-(k*(p.1-a+(p.2-c)))) * ‖F p-G p‖ ≤ B at hm
    rw [Real.exp_neg] at hm
    apply (div_le_iff₀ (Real.exp_pos _)).mp
    simpa only [div_eq_mul_inv,mul_comm] using hm
  have hεp p (hp : p ∈ Icc a b ×ˢ Icc c d) :
      ε ≤ ε*Real.exp (k*(p.1-a+(p.2-c))) := by
    have hexp : 1 ≤ Real.exp (k*(p.1-a+(p.2-c))) :=
      Real.one_le_exp (mul_nonneg hk.le (add_nonneg (sub_nonneg.mpr hp.1.1)
        (sub_nonneg.mpr hp.2.1)))
    simpa using mul_le_mul_of_nonneg_left hexp hε
  have hi u (hu : u ∈ Icc a b) v (hv : v ∈ Icc c d) :
      ‖(F (u,v)).1-(G (u,v)).1‖ ≤
        (ε+(K/k)*B)*Real.exp (k*(u-a+(v-c))) := by
    have hd : ‖∫ s in a..u, fi (F (s,v))-fi (G (s,v))‖ ≤
        (K/k)*B*Real.exp (k*(u-a+(v-c))) := by
      apply Broad.norm_integral_le_exponential_of_bound hu.1 hk hK hB
      intro s hs
      have hp : (s,v) ∈ Icc a b ×ˢ Icc c d := ⟨⟨hs.1.le,hs.2.trans hu.2⟩,hv⟩
      exact (hLi (s,v) hp).trans
        ((mul_le_mul_of_nonneg_left (hbound (s,v) hp) hK).trans_eq (by ring))
    have heq : (F (u,v)).1-(G (u,v)).1 =
        (∫ s in a..u, fi (F (s,v))-fi (G (s,v))) +
        (yi v + (∫ s in a..u, fi (G (s,v)))-(G (u,v)).1) := by
      rw [intervalIntegral.integral_sub (f := fun s => fi (F (s,v))) (g := fun s => fi (G (s,v)))
        (((hfi.comp hF).comp (show Continuous (fun s : ℝ => (s,v)) by fun_prop)).intervalIntegrable
            (μ := volume) a u)
        (((hfi.comp hG).comp (show Continuous (fun s : ℝ => (s,v)) by fun_prop)).intervalIntegrable
            (μ := volume) a u), hFi u hu v hv]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hd
      ((hGi u hu v hv).trans (hεp (u,v) ⟨hu,hv⟩))).trans_eq (by ring))
  have ho u (hu : u ∈ Icc a b) v (hv : v ∈ Icc c d) :
      ‖(F (u,v)).2-(G (u,v)).2‖ ≤
        (ε+(K/k)*B)*Real.exp (k*(u-a+(v-c))) := by
    have hd : ‖∫ t in c..v, fo (F (u,t))-fo (G (u,t))‖ ≤
        (K/k)*B*Real.exp (k*(u-a+(v-c))) := by
      have hd := Broad.norm_integral_le_exponential_of_bound hv.1 hk hK hB
        (y := u-a) (f := fun t => fo (F (u,t))-fo (G (u,t))) (fun t ht => by
          have hp : (u,t) ∈ Icc a b ×ˢ Icc c d := ⟨hu,ht.1.le,ht.2.trans hv.2⟩
          apply (hLo (u,t) hp).trans
          rw [show t-c+(u-a)=u-a+(t-c) by ring]
          exact (mul_le_mul_of_nonneg_left (hbound (u,t) hp) hK).trans_eq (by ring))
      simpa only [show v-c+(u-a)=u-a+(v-c) by ring] using hd
    have heq : (F (u,v)).2-(G (u,v)).2 =
        (∫ t in c..v, fo (F (u,t))-fo (G (u,t))) +
        (xb u + (∫ t in c..v, fo (G (u,t)))-(G (u,v)).2) := by
      rw [intervalIntegral.integral_sub (f := fun t => fo (F (u,t))) (g := fun t => fo (G (u,t)))
        (((hfo.comp hF).comp (show Continuous (fun t : ℝ => (u,t)) by fun_prop)).intervalIntegrable
            (μ := volume) c v)
        (((hfo.comp hG).comp (show Continuous (fun t : ℝ => (u,t)) by fun_prop)).intervalIntegrable
            (μ := volume) c v), hFo u hu v hv]
      abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hd
      ((hGo u hu v hv).trans (hεp (u,v) ⟨hu,hv⟩))).trans_eq (by ring))
  have hself : B ≤ ε+(K/k)*B := by
    have hfull : ‖F p₀-G p₀‖ ≤ (ε+(K/k)*B)*Real.exp (k*(p₀.1-a+(p₀.2-c))) :=
      max_le (hi p₀.1 hp₀.1 p₀.2 hp₀.2) (ho p₀.1 hp₀.1 p₀.2 hp₀.2)
    have hm := mul_le_mul_of_nonneg_left hfull (Real.exp_pos (-(k*(p₀.1-a+(p₀.2-c))))).le
    apply hm.trans_eq
    rw [Real.exp_neg]
    field_simp
  have hratio : K/k ≤ 1/2 := (div_le_iff₀ hk).mpr (by linarith)
  have hBε : B ≤ 2*ε := by
    have := mul_le_mul_of_nonneg_right hratio hB
    linarith
  intro p hp
  exact (hbound p hp).trans (mul_le_mul_of_nonneg_right hBε (Real.exp_pos _).le)

/-- Construct the continuous characteristic state within an explicit
residual-controlled distance of a reference. The exponential coefficient
is determined only by the global source Lipschitz coefficient `L`, before
the rectangle, traces, reference and residual size are chosen. -/
theorem continuous_rectangle_goursat_near_reference
    {a b c d ε : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hε : 0 ≤ ε)
    {L : ℝ≥0} (fi : X × Y → X) (fo : X × Y → Y)
    (yi : ℝ → X) (xb : ℝ → Y) (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo)
    (hyi : Continuous yi) (hxb : Continuous xb) (G : ℝ × ℝ → X × Y) (hG : Continuous G)
    (hGi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      ‖yi v + (∫ s in a..u, fi (G (s, v))) - (G (u, v)).1‖ ≤ ε)
    (hGo : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      ‖xb u + (∫ t in c..v, fo (G (u, t))) - (G (u, v)).2‖ ≤ ε) :
    ∃ F : ℝ × ℝ → X × Y, Continuous F ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        (F (u,v)).1 = yi v + ∫ s in a..u, fi (F (s,v))) ∧
      (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
        (F (u,v)).2 = xb u + ∫ t in c..v, fo (F (u,t))) ∧
      (∀ p ∈ Icc a b ×ˢ Icc c d,
        ‖F p-G p‖ ≤ 2*ε*Real.exp ((2*(L+1))*(p.1-a+(p.2-c)))) := by
  obtain ⟨F,hF,hFi,hFo⟩ := continuous_rectangle_goursat hab hcd fi fo yi xb hfi hfo hyi hxb
  refine ⟨F,hF,hFi,hFo,?_⟩
  apply rectangle_goursat_distance_of_residual hab hcd L.coe_nonneg
    (by positivity : 0 < (2*((L:ℝ)+1))) (by linarith) hε
    hF hG hfi.continuous hfo.continuous hFi hFo hGi hGo
  · intro p _hp
    exact lipschitz_norm_sub_le hfi _ _
  · intro p _hp
    exact lipschitz_norm_sub_le hfo _ _

/-- Fixed compact carrier for parameter-dependent characteristic rectangles. -/
abbrev StripUnitSquare := Icc (0 : ℝ) 1 × Icc (0 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private noncomputable def stripWeightedValue (γ : ℝ) (z : C(StripUnitSquare, E))
    (p : ℝ × ℝ) : E :=
  rectWeight 0 0 γ p • z (clampRect zero_le_one zero_le_one p)

omit [CompleteSpace E] in
private theorem continuous_stripWeightedValue (γ : ℝ) (z : C(StripUnitSquare, E)) :
    Continuous (stripWeightedValue γ z) := by
  have hw : Continuous (fun p : ℝ × ℝ => Real.exp (γ*(p.1-0+(p.2-0)))) := by fun_prop
  exact hw.smul (z.continuous.comp (continuous_clampRect zero_le_one zero_le_one))

private noncomputable def stripIncomingPrimitiveFunction (γ : ℝ)
    (z : C(StripUnitSquare, E)) : C(StripUnitSquare,E) := by
  let F := stripWeightedValue γ z
  have hF := continuous_stripWeightedValue γ z
  have hi := continuous_variable_integral F hF 0
  let r : StripUnitSquare → ℝ × ℝ := fun p => (p.1,p.2)
  have hr : Continuous r := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)
  have hw : Continuous (fun p : ℝ × ℝ => Real.exp (γ*(p.1-0+(p.2-0)))) := by fun_prop
  exact ⟨fun p => (rectWeight 0 0 γ (r p))⁻¹ • ∫ s in 0..(r p).1, F (s,(r p).2),
    ((hw.inv₀ (fun p => (Real.exp_pos _).ne')).smul hi).comp hr⟩

private theorem norm_stripIncomingPrimitiveFunction_le {γ : ℝ} (hγ : 0 < γ)
    (z : C(StripUnitSquare, E)) :
    ‖stripIncomingPrimitiveFunction γ z‖ ≤ γ⁻¹*‖z‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (inv_pos.mpr hγ).le (norm_nonneg _))).mpr
  intro p
  have hi : ‖∫ s in 0..(p.1 : ℝ), stripWeightedValue γ z (s,p.2)‖ ≤
      (1/γ)*‖z‖*rectWeight 0 0 γ (p.1,p.2) := by
    apply Broad.norm_integral_le_exponential_of_bound p.1.property.1 hγ zero_le_one
      (norm_nonneg z)
    intro s _hs
    dsimp only [stripWeightedValue]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < rectWeight 0 0 γ (s,p.2) from Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (z.norm_coe_le_norm _) (Real.exp_pos _).le).trans_eq
      (by dsimp [rectWeight]; ring)
  change ‖(rectWeight 0 0 γ (p.1,p.2))⁻¹ •
    ∫ s in 0..(p.1 : ℝ), stripWeightedValue γ z (s,p.2)‖ ≤ _
  have hwp : 0 < rectWeight 0 0 γ (p.1,p.2) := Real.exp_pos _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwp)]
  refine (mul_le_mul_of_nonneg_left hi (inv_pos.mpr hwp).le).trans_eq ?_
  calc
    _ = ((rectWeight 0 0 γ (p.1,p.2))⁻¹ * rectWeight 0 0 γ (p.1,p.2)) * ((1/γ)*‖z‖) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hwp.ne',one_mul,one_div]

/-- Weighted incoming Volterra primitive. Its norm is at most `γ⁻¹`,
uniformly in the Banach-valued continuous function. -/
noncomputable def stripWeightedIncomingIntegral (γ : ℝ) (hγ : 0 < γ) :
    C(StripUnitSquare,E) →L[ℝ] C(StripUnitSquare,E) := by
  let P : C(StripUnitSquare,E) →ₗ[ℝ] C(StripUnitSquare,E) :=
    { toFun := stripIncomingPrimitiveFunction γ
      map_add' := by
        intro z w
        ext p
        change (rectWeight 0 0 γ (p.1,p.2))⁻¹ •
          (∫ s in 0..(p.1 : ℝ), stripWeightedValue γ (z+w) (s,p.2)) = _
        have hadd s : stripWeightedValue γ (z+w) (s,p.2) =
            stripWeightedValue γ z (s,p.2) + stripWeightedValue γ w (s,p.2) := by
          simp [stripWeightedValue, smul_add]
        simp_rw [hadd]
        rw [intervalIntegral.integral_add
          (f := fun s => stripWeightedValue γ z (s,p.2))
          (g := fun s => stripWeightedValue γ w (s,p.2))
          (((continuous_stripWeightedValue γ z).comp
            (show Continuous (fun s : ℝ => (s,(p.2 : ℝ))) by fun_prop)).intervalIntegrable (μ :=
                volume) 0 p.1)
          (((continuous_stripWeightedValue γ w).comp
            (show Continuous (fun s : ℝ => (s,(p.2 : ℝ))) by fun_prop)).intervalIntegrable (μ :=
                volume) 0 p.1), smul_add]
        rfl
      map_smul' := by
        intro q z
        ext p
        change (rectWeight 0 0 γ (p.1,p.2))⁻¹ •
          (∫ s in 0..(p.1 : ℝ), stripWeightedValue γ (q • z) (s,p.2)) = _
        have hsmul s : stripWeightedValue γ (q • z) (s,p.2) =
            q • stripWeightedValue γ z (s,p.2) := by
          exact smul_comm _ _ _
        simp_rw [hsmul, intervalIntegral.integral_smul]
        exact smul_comm _ _ _ }
  exact P.mkContinuous (γ⁻¹) (norm_stripIncomingPrimitiveFunction_le hγ)

/-- The incoming weighted primitive has the explicit exponential gain
`γ⁻¹`; the bound is independent of the target Banach space and input. -/
theorem norm_stripWeightedIncomingIntegral_le {γ : ℝ} (hγ : 0 < γ) :
    ‖stripWeightedIncomingIntegral (E := E) γ hγ‖ ≤ γ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hγ).le
  exact norm_stripIncomingPrimitiveFunction_le hγ

/-- Pointwise formula for the weighted incoming Volterra primitive.
The clamping only specifies the integrand outside the integration interval. -/
theorem stripWeightedIncomingIntegral_apply (γ : ℝ) (hγ : 0 < γ)
    (z : C(StripUnitSquare, E)) (p : StripUnitSquare) :
    stripWeightedIncomingIntegral γ hγ z p =
      Real.exp (-(γ*((p.1 : ℝ)+(p.2 : ℝ)))) •
        ∫ s in 0..(p.1 : ℝ), Real.exp (γ*(s+(p.2 : ℝ))) •
          z (projIcc 0 1 zero_le_one s,p.2) := by
  change (rectWeight 0 0 γ (p.1,p.2))⁻¹ •
    (∫ s in 0..(p.1 : ℝ), stripWeightedValue γ z (s,p.2)) = _
  simp only [stripWeightedValue,clampRect,rectWeight,sub_zero,Real.exp_neg,
    projIcc_of_mem zero_le_one p.2.property]

private def stripSquareSwap : C(StripUnitSquare,StripUnitSquare) :=
  ⟨Prod.swap,continuous_swap⟩

private noncomputable def stripSwapCLM :
    C(StripUnitSquare,E) →L[ℝ] C(StripUnitSquare,E) :=
  ContinuousMap.compCLM ℝ E stripSquareSwap

omit [CompleteSpace E] in
private theorem norm_stripSwapCLM_apply_le (z : C(StripUnitSquare, E)) :
    ‖stripSwapCLM z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro p
  exact z.norm_coe_le_norm _

/-- Weighted outgoing Volterra primitive, obtained by interchanging the
coordinates of the fixed square. The weight treats both directions equally. -/
noncomputable def stripWeightedOutgoingIntegral (γ : ℝ) (hγ : 0 < γ) :
    C(StripUnitSquare,E) →L[ℝ] C(StripUnitSquare,E) :=
  stripSwapCLM.comp ((stripWeightedIncomingIntegral γ hγ).comp stripSwapCLM)

/-- The outgoing weighted primitive has the same dimension-independent
operator norm bound `γ⁻¹`. -/
theorem norm_stripWeightedOutgoingIntegral_le {γ : ℝ} (hγ : 0 < γ) :
    ‖stripWeightedOutgoingIntegral (E := E) γ hγ‖ ≤ γ⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_pos.mpr hγ).le
  intro z
  exact (norm_stripSwapCLM_apply_le _).trans
    ((norm_stripIncomingPrimitiveFunction_le hγ _).trans
      (mul_le_mul_of_nonneg_left (norm_stripSwapCLM_apply_le z) (inv_pos.mpr hγ).le))

/-- Pointwise outgoing formula, with exactly the same exponential weight
as the incoming primitive. -/
theorem stripWeightedOutgoingIntegral_apply (γ : ℝ) (hγ : 0 < γ)
    (z : C(StripUnitSquare, E)) (p : StripUnitSquare) :
    stripWeightedOutgoingIntegral γ hγ z p =
      Real.exp (-(γ*((p.1 : ℝ)+(p.2 : ℝ)))) •
        ∫ t in 0..(p.2 : ℝ), Real.exp (γ*((p.1 : ℝ)+t)) •
          z (p.1,projIcc 0 1 zero_le_one t) := by
  change stripWeightedIncomingIntegral γ hγ (stripSwapCLM z) (p.2,p.1) = _
  rw [stripWeightedIncomingIntegral_apply]
  simp only [stripSwapCLM,ContinuousMap.compCLM_apply,ContinuousMap.comp_apply,
    stripSquareSwap,ContinuousMap.coe_mk,Prod.swap_prod_mk]
  rw [show (p.2 : ℝ)+(p.1 : ℝ)=(p.1 : ℝ)+(p.2 : ℝ) by ring]
  congr 1
  apply congrArg (fun f : ℝ → E => ∫ t in 0..(p.2 : ℝ), f t)
  funext t
  rw [add_comm t (p.1 : ℝ)]


end EmcsfAcExtension.Local
