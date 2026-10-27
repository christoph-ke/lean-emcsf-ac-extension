module

public import EmcsfAcExtension.Global.Exterior.VariationTailsDuhamel
public import EmcsfAcExtension.Global.Exterior.VariationTails

/-! # Decay from a fixed proper row

The initial contribution is an ordinary L¹ tail on one selected row.
The source contribution is a complete integrable time tail, and its
multiplier is fixed before both rows. This proves internal project record (D2)–(D1),
`charged_SF_new_version.tex:L1381–L1391`, without uniform initial derivative moduli.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The integrated Duhamel estimate on the precise proper rectangle
`[s,u] × [t(u),0]`. The multiplier depends only on the complete coefficient
integral, uniformly in both rows and every surviving label. -/
theorem outgoing_variation_duhamel_of_majorants
    {ui e c s u KV : ℝ} {S : Fields} {t k q : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0)
    (hroot : ∀ x ∈ Ico c 0, x < t x ∧ t x ≤ 0)
    (hm : MonotoneOn t (Ico c 0))
    (hcs : c ≤ s) (hsu : s ≤ u) (hu : u < 0)
    (hk : IntervalIntegrable k volume c 0) (hq : IntervalIntegrable q volume c 0)
    (hk₀ : ∀ x ∈ Ico c 0, 0 ≤ k x)
    (hcoef : ∀ x ∈ Ico c 0, ∀ v ∈ Icc (t x) 0, |S.rUV x v / S.lam x v| ≤ k x)
    (hvar : ∀ x ∈ Ico c 0, (eVariationOn (S.a x) (Icc (t x) 0)).toReal ≤ KV)
    (hsource : ∀ x ∈ Ico c 0, (∫ v in t x..0, ‖rawDensitySource e S x v‖) ≤
      k x * (eVariationOn (S.a x) (Icc (t x) 0)).toReal + q x) :
    (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤
      Real.exp (∫ x in c..0, k x) * (∫ v in t u..0, ‖deriv (S.a s) v‖) +
      Real.exp (∫ x in c..0, k x) * (∫ x in s..u, (k x * KV + q x)) := by
  have hlate (x : ℝ) (hx : x ∈ Icc s u) : x ∈ Ico c 0 :=
    ⟨hcs.trans hx.1, hx.2.trans_lt hu⟩
  have hur : u ∈ Ico c 0 := ⟨hcs.trans hsu, hu⟩
  have htu := hroot u hur
  have hmem (x : ℝ) (hx : x ∈ Icc s u) : (x, t x) ∈ origDomain ui :=
    ⟨hc.1.le.trans (hlate x hx).1, (hlate x hx).2, (hroot x (hlate x hx)).1.le,
      (hroot x (hlate x hx)).2⟩
  have hproper (x : ℝ) (hx : x ∈ Icc s u) : x < t x := (hroot x (hlate x hx)).1
  have hW := (swept_density_row_primitive h.solution hsu hmem hproper ⟨hsu, le_rfl⟩).1
  have hTV := swept_row_variation_eq_density_integral h.solution hsu hmem hproper ⟨hsu, le_rfl⟩
  have hrect : Icc s u ×ˢ Icc (t u) 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hxv := hx.2.trans_lt (htu.1.trans_le hv.1)
    exact ⟨⟨hc.1.le.trans (hcs.trans hx.1), hxv.trans_le hv.2, hxv.le, hv.2⟩, hxv⟩
  have cF := (Calculus.continuousOn_rawDensitySource h.solution hrect).norm
  have hFI : IntegrableOn (fun p => ‖rawDensitySource e S p.1 p.2‖)
      (Icc s u ×ˢ Icc (t u) 0) (volume.prod volume) :=
    cF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hFProd : Integrable (fun p : ℝ × ℝ => ‖rawDensitySource e S p.1 p.2‖)
      ((volume.restrict (Icc s u)).prod (volume.restrict (Icc (t u) 0))) := by
    rwa [Measure.prod_restrict]
  have hFt : IntervalIntegrable (fun v => ∫ x in s..u, ‖rawDensitySource e S x v‖)
      volume (t u) 0 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le htu.2).2
    apply hFProd.integral_prod_right.congr
    filter_upwards [] with v
    rw [intervalIntegral.integral_of_le hsu, ← integral_Icc_eq_integral_Ioc]
  have hsout : outSeg s (t u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨rfl, hv⟩
    exact (hrect ⟨⟨le_rfl, hsu⟩, hv⟩).1
  have hw₀ := (h.solution.ac_out s (t u) 0 htu.2 hsout).2.2.2.2.intervalIntegrable_deriv_complex
  have hpoint (v : ℝ) (hv : v ∈ Icc (t u) 0) :=
    density_duhamel_bound_of_ratio h.solution (hc.1.le.trans hcs) hsu
      (htu.1.trans_le hv.1) hv.2
      (lambda_ratio_le_of_integrable_majorant h ⟨hc.1.le, hc.2⟩ hcs hsu
        (htu.1.trans_le hv.1) hv.2 hk hk₀ (fun x hx =>
          hcoef x (hlate x hx) v
            ⟨(hm (hlate x hx) hur hx.2).trans hv.1, hv.2⟩))
  let P := Real.exp (∫ x in c..0, k x)
  have hi := intervalIntegral.integral_mono_on htu.2 hW.norm
    ((hw₀.norm.const_mul P).add (hFt.const_mul P)) hpoint
  rw [intervalIntegral.integral_add (hw₀.norm.const_mul P) (hFt.const_mul P),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hTV] at hi
  have hswap := Density.integral_integral_swap_rectangle
    (a := s) (b := u) (c := t u) (d := 0)
    (H := fun x v => ‖rawDensitySource e S x v‖)
    (hFI.mono_set (by
      rw [uIoc_of_le hsu, uIoc_of_le htu.2]
      exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
  rw [← hswap] at hi
  have hsub : uIcc s u ⊆ uIcc c 0 := by
    rw [uIcc_of_le hsu, uIcc_of_le hc.2.le]
    exact Icc_subset_Icc hcs hu.le
  have hJ := ((hk.mul_const KV).add hq).mono_set hsub
  have hrowbound (x : ℝ) (hx : x ∈ Icc s u) :
      (∫ v in t u..0, ‖rawDensitySource e S x v‖) ≤ k x * KV + q x := by
    have hxr := hroot x (hlate x hx)
    have hout : outSeg x (t x) 0 ⊆ origDomain ui :=
      (outSeg_subset_origDomain_iff hxr.2).2
        ⟨hc.1.le.trans (hlate x hx).1, (hlate x hx).2, hxr.1.le, le_rfl⟩
    have houtproper : outSeg x (t x) 0 ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
      intro p hp
      refine ⟨hout hp, ?_⟩
      rcases hp with ⟨rfl, hp⟩
      exact hxr.1.trans_le hp.1
    have hSourceCont : ContinuousOn (fun v => rawDensitySource e S x v) (Icc (t x) 0) :=
      (Calculus.continuousOn_rawDensitySource h.solution houtproper).comp
        (f := fun v : ℝ => (x, v))
        (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨rfl, hv⟩)
    have hSourceI : IntervalIntegrable (fun v => ‖rawDensitySource e S x v‖) volume (t x) 0 :=
      hSourceCont.norm.intervalIntegrable_of_Icc hxr.2
    have hinc := intervalIntegral.integral_mono_interval
      (hm (hlate x hx) hur hx.2) htu.2 le_rfl
      (Eventually.of_forall fun v => norm_nonneg (rawDensitySource e S x v)) hSourceI
    exact hinc.trans ((hsource x (hlate x hx)).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hvar x (hlate x hx)) (hk₀ x (hlate x hx))) le_rfl))
  have houter : (∫ x in s..u, ∫ v in t u..0, ‖rawDensitySource e S x v‖) ≤
      ∫ x in s..u, (k x * KV + q x) := by
    rw [intervalIntegral.integral_of_le hsu, intervalIntegral.integral_of_le hsu]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x =>
        intervalIntegral.integral_nonneg htu.2 (fun _ _ => norm_nonneg _)) hJ.1
    exact (ae_restrict_mem measurableSet_Ioc).mono fun x hx => hrowbound x ⟨hx.1.le, hx.2⟩
  exact hi.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left houter (Real.exp_pos _).le))

/-- [internal]
Actual outgoing variation tends to zero from the proved uniform bound,
the pointwise optical coefficient bound, and the actual source majorant.
Only a fixed-row L¹ derivative tail is used. The multiplier is fixed by
the complete coefficient integral before selecting either later row. -/
theorem outgoing_variation_decay_of_majorants
    {ui e c KV : ℝ} {S : Fields} {t k q : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0)
    (hroot : ∀ x ∈ Ico c 0, x < t x ∧ t x ≤ 0)
    (hm : MonotoneOn t (Ico c 0)) (ht : Tendsto t (𝓝[<] 0) (𝓝 0))
    (hk : IntervalIntegrable k volume c 0) (hq : IntervalIntegrable q volume c 0)
    (hk₀ : ∀ x ∈ Ico c 0, 0 ≤ k x) (hq₀ : ∀ x ∈ Ico c 0, 0 ≤ q x)
    (hKV : 0 ≤ KV)
    (hcoef : ∀ x ∈ Ico c 0, ∀ v ∈ Icc (t x) 0, |S.rUV x v / S.lam x v| ≤ k x)
    (hvar : ∀ x ∈ Ico c 0, (eVariationOn (S.a x) (Icc (t x) 0)).toReal ≤ KV)
    (hsource : ∀ x ∈ Ico c 0, (∫ v in t x..0, ‖rawDensitySource e S x v‖) ≤
      k x * (eVariationOn (S.a x) (Icc (t x) 0)).toReal + q x) :
    Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0) := by
  let P := Real.exp (∫ x in c..0, k x)
  let J := fun x => k x * KV + q x
  have hJ : IntervalIntegrable J volume c 0 := (hk.mul_const KV).add hq
  have hJ₀ (x : ℝ) (hx : x ∈ Ico c 0) : 0 ≤ J x :=
    add_nonneg (mul_nonneg (hk₀ x hx) hKV) (hq₀ x hx)
  have hT : Tendsto (fun s => P * (∫ x in s..0, J x)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [mul_zero] using (time_integral_tail_tendsto hc.2 hJ).const_mul P
  apply outgoing_variation_decay_of_duhamel h t (fun s => P * ∫ x in s..0, J x)
    hc (Real.exp_pos _).le ht hroot hm hT
  · intro s hs u hu
    have hD := outgoing_variation_duhamel_of_majorants h hc hroot hm hs.1.le hu.1.le hu.2
      hk hq hk₀ hcoef hvar hsource
    have hsub : uIcc s 0 ⊆ uIcc c 0 := by
      rw [uIcc_of_le hs.2.le, uIcc_of_le hc.2.le]
      exact Icc_subset_Icc hs.1.le le_rfl
    have hle := intervalIntegral.integral_mono_interval le_rfl hu.1.le hu.2.le
      (by
        rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
        filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
        exact hJ₀ x ⟨hs.1.le.trans hx.1, hx.2⟩) (hJ.mono_set hsub)
    exact hD.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le))

/-- [internal] The common M5 right side tends to zero, uniformly before
any admissible boundary or final time is chosen. Its constants are those
of the already established variation and forcing estimates. -/
theorem variation_exit_majorant_tendsto_zero
    {c KV : ℝ} {S : Fields} {t k q : ℝ → ℝ}
    (hc : c < 0) (hk : IntervalIntegrable k volume c 0)
    (hq : IntervalIntegrable q volume c 0)
    (hV : Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal)
      (𝓝[<] 0) (𝓝 0)) :
    Tendsto (fun a => (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
      ∫ u in a..0, (k u * KV + q u)) (𝓝[<] 0) (𝓝 0) := by
  simpa only [add_zero] using hV.add
    (time_integral_tail_tendsto hc ((hk.mul_const KV).add hq))

end EmcsfAcExtension.Global.Exterior
