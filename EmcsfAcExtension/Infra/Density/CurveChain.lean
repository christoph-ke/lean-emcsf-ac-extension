module

public import EmcsfAcExtension.Infra.Density.Representative
public import EmcsfAcExtension.Infra.AC.Relabel

/-!
# Absolute continuity on monotone curves from a fixed label density

The proof uses rectangular increments and an AC control function. It never
restricts a two-dimensional almost-everywhere derivative to a curve.
-/

public section

open Set MeasureTheory Filter Asymptotics
open scoped Topology NNReal

namespace EmcsfAcExtension.Global.Density

/-- [internal] A curve controlled in distance by an AC curve is AC. This helper
is used with the sum of an incoming Lipschitz control and a label primitive. -/
theorem absolutelyContinuousOnInterval_of_dist_le_control
    {E H : Type*} [PseudoMetricSpace E] [PseudoMetricSpace H]
    {f : ℝ → E} {q : ℝ → H} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hbound : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, dist (f s) (f t) ≤ dist (q s) (q t)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hq ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hq ε hε
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hI hlen
  apply lt_of_le_of_lt _ (hδε (n, I) hI hlen)
  exact Finset.sum_le_sum fun i hi => hbound _ (hI.1 i hi).1 _ (hI.1 i hi).2

/-- [internal] A represented function has an AC trace along monotone AC labels.
The incoming Lipschitz constant is the displayed `M`; the outgoing control is
the single integrable label function `B`, uniform in the incoming parameter.
Neither a pointwise outgoing derivative nor a product-a.e. trace is assumed. -/
theorem absolutelyContinuousOnInterval_trace_of_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f W : ℝ → ℝ → E} {B U V : ℝ → ℝ} {a b : ℝ} {M : ℝ≥0}
    (hU : AbsolutelyContinuousOnInterval U a b)
    (hV : AbsolutelyContinuousOnInterval V a b)
    (hUm : MonotoneOn U (uIcc a b)) (hVm : MonotoneOn V (uIcc a b))
    (hB : IntervalIntegrable B volume (V a) (V b))
    (hin : ∀ v ∈ uIcc (V a) (V b),
      LipschitzOnWith M (fun u => f u v) (uIcc (U a) (U b)))
    (hW : ∀ u ∈ uIcc (U a) (U b),
      IntervalIntegrable (W u) volume (V a) (V b))
    (hbound : ∀ u ∈ uIcc (U a) (U b), ∀ v ∈ uIcc (V a) (V b), ‖W u v‖ ≤ B v)
    (hrep : ∀ u ∈ uIcc (U a) (U b), ∀ v ∈ uIcc (V a) (V b),
      f u v = f u (V a) + ∫ s in V a..v, W u s) :
    AbsolutelyContinuousOnInterval (fun t => f (U t) (V t)) a b := by
  let q : ℝ → ℝ := fun t => (M : ℝ) * U t + ∫ s in V a..V t, B s
  have hq : AbsolutelyContinuousOnInterval q a b :=
    (hU.const_mul M).add
      ((hB.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).comp_monotoneOn
        hV hVm)
  apply absolutelyContinuousOnInterval_of_dist_le_control hq
  have hmapU (t : ℝ) (ht : t ∈ uIcc a b) : U t ∈ uIcc (U a) (U b) :=
    hUm.image_uIcc_subset ⟨t, ht, rfl⟩
  have hmapV (t : ℝ) (ht : t ∈ uIcc a b) : V t ∈ uIcc (V a) (V b) :=
    hVm.image_uIcc_subset ⟨t, ht, rfl⟩
  suffices hordered : ∀ s ∈ uIcc a b, ∀ t ∈ uIcc a b, s ≤ t →
      dist (f (U s) (V s)) (f (U t) (V t)) ≤ dist (q s) (q t) by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hordered s hs t ht hst
    · simpa only [dist_comm] using hordered t ht s hs hts
  intro s hs t ht hst
  have hUs := hmapU s hs
  have hUt := hmapU t ht
  have hVs := hmapV s hs
  have hVt := hmapV t ht
  have hVst := hVm hs ht hst
  have hUst := hUm hs ht hst
  have hsub : uIcc (V s) (V t) ⊆ uIcc (V a) (V b) :=
    uIcc_subset_uIcc hVs hVt
  have hrow : f (U s) (V t) - f (U s) (V s) = ∫ v in V s..V t, W (U s) v := by
    rw [hrep _ hUs _ hVt, hrep _ hUs _ hVs, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left
        ((hW _ hUs).mono_set (uIcc_subset_uIcc left_mem_uIcc hVt))
        ((hW _ hUs).mono_set (uIcc_subset_uIcc left_mem_uIcc hVs))]
  have hout : dist (f (U s) (V s)) (f (U s) (V t)) ≤ ∫ v in V s..V t, B v := by
    rw [dist_comm, dist_eq_norm, hrow]
    exact intervalIntegral.norm_integral_le_of_norm_le hVst
      (ae_of_all _ fun v hv => hbound _ hUs v (hsub (by
        rw [uIcc_of_le hVst]; exact Ioc_subset_Icc_self hv)))
      (hB.mono_set hsub)
  have hinner := (hin _ hVt).dist_le_mul _ hUs _ hUt
  have hcontrol : (∫ v in V s..V t, B v) + (M : ℝ) * dist (U s) (U t) = q t - q s := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hUst), neg_sub]
    dsimp only [q]
    rw [← intervalIntegral.integral_interval_sub_left
      (hB.mono_set (uIcc_subset_uIcc left_mem_uIcc hVt))
      (hB.mono_set (uIcc_subset_uIcc left_mem_uIcc hVs))]
    ring
  calc
    dist (f (U s) (V s)) (f (U t) (V t)) ≤
        dist (f (U s) (V s)) (f (U s) (V t)) +
          dist (f (U s) (V t)) (f (U t) (V t)) := dist_triangle _ _ _
    _ ≤ (∫ v in V s..V t, B v) + (M : ℝ) * dist (U s) (U t) := add_le_add hout hinner
    _ = q t - q s := hcontrol
    _ ≤ dist (q s) (q t) := by rw [dist_comm, Real.dist_eq]; exact le_abs_self _

/-- [internal] A local chain rule needs only one continuous partial derivative
and the other sectional derivative at the actual label. Thus a common set of
good labels can be pulled back before applying this theorem. -/
theorem hasDerivAt_trace_of_continuous_incoming_partial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f G : ℝ → ℝ → E} {U V : ℝ → ℝ} {t U' V' : ℝ} {W : E}
    (hU : HasDerivAt U U' t) (hV : HasDerivAt V V' t)
    (hG : ContinuousAt G.uncurry (U t, V t))
    (hin : ∀ᶠ p : ℝ × ℝ in 𝓝 (U t, V t),
      HasDerivAt (fun u => f u p.2) (G p.1 p.2) p.1)
    (hout : HasDerivAt (f (U t)) W (V t)) :
    HasDerivAt (fun s => f (U s) (V s)) (U' • G (U t) (V t) + V' • W) t := by
  let z : ℝ → E := fun s =>
    f (U s) (V s) - f (U t) (V s) - (U s - U t) • G (U t) (V t)
  have hsmall : z =o[𝓝 t] (fun s => U s - U t) := by
    apply IsLittleO.of_bound
    intro ε hε
    have hclose : ∀ᶠ p : ℝ × ℝ in 𝓝 (U t, V t),
        HasDerivAt (fun u => f u p.2) (G p.1 p.2) p.1 ∧
          ‖G p.1 p.2 - G (U t) (V t)‖ ≤ ε := by
      filter_upwards [hin, hG.eventually (Metric.ball_mem_nhds _ hε)] with p hp hpg
      exact ⟨hp, le_of_lt (by
        simpa only [Metric.mem_ball, dist_eq_norm, Function.uncurry] using hpg)⟩
    obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff.mp hclose
    have huv := hU.continuousAt.prodMk hV.continuousAt
    filter_upwards [huv.eventually (Metric.ball_mem_nhds _ hδ)] with s hs
    have hseg : ∀ u ∈ uIcc (U t) (U s),
        HasDerivAt (fun x => f x (V s)) (G u (V s)) u ∧
          ‖G u (V s) - G (U t) (V t)‖ ≤ ε := by
      intro u hu
      apply hδall (y := (u, V s))
      rw [Prod.dist_eq, max_lt_iff] at hs
      rw [Prod.dist_eq, max_lt_iff]
      refine ⟨?_, hs.2⟩
      have hdist : dist u (U t) ≤ dist (U s) (U t) := by
        rw [Real.dist_eq, Real.dist_eq, abs_le]
        rcases le_total (U t) (U s) with hts | hst
        · rw [uIcc_of_le hts] at hu
          rw [abs_of_nonneg (sub_nonneg.mpr hts)]
          constructor <;> linarith [hu.1, hu.2]
        · rw [uIcc_of_ge hst] at hu
          rw [abs_of_nonpos (sub_nonpos.mpr hst)]
          constructor <;> linarith [hu.1, hu.2]
      exact hdist.trans_lt hs.1
    have hd : ∀ u ∈ uIcc (U t) (U s),
        HasDerivWithinAt (fun x => f x (V s) - x • G (U t) (V t))
          (G u (V s) - G (U t) (V t)) (uIcc (U t) (U s)) u := by
      intro u hu
      simpa only [Pi.sub_def, id_eq, one_smul] using
        ((hseg u hu).1.sub ((hasDerivAt_id u).smul_const (G (U t) (V t)))).hasDerivWithinAt
    have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun u hu => (hseg u hu).2) (convex_uIcc (U t) (U s))
      left_mem_uIcc right_mem_uIcc
    convert hb using 1
    congr 1
    dsimp only [z]
    rw [sub_smul]
    abel
  have hzt : z t = 0 := by simp [z]
  have hdz : HasDerivAt z 0 t := by
    apply HasDerivAt.of_isLittleO
    simpa only [hzt, sub_zero, smul_zero] using hsmall.trans_isBigO hU.isBigO_sub
  have hd := (hdz.add ((hU.sub_const (U t)).smul_const (G (U t) (V t)))).add
    (hout.scomp t hV)
  convert hd using 1
  · funext s
    dsimp only [Pi.add_apply, Function.comp_apply, z]
    abel
  · simp only [zero_add]

/-- [internal] An inverse Lipschitz bound on a label map pulls a null set of
labels back to a null set of parameters. No measurability of the exceptional
set is required. The constant is the displayed inverse Lipschitz bound `L`. -/
theorem ae_pullback_of_antilipschitzOn {V : ℝ → ℝ} {s : Set ℝ} {L : ℝ≥0}
    (hs : MeasurableSet s) (hV : AntilipschitzWith L (s.domRestrict V))
    {Q : ℝ → Prop} (hQ : ∀ᵐ v, Q v) :
    ∀ᵐ t ∂volume.restrict s, Q (V t) := by
  classical
  let N : Set ℝ := {v | ¬ Q v}
  have hN : volume N = 0 := hQ
  let A : Set s := (s.domRestrict V) ⁻¹' N
  have hA : Measure.hausdorffMeasure 1 A = 0 := by
    simpa [A, hN] using
      hV.hausdorffMeasure_preimage_le (d := 1) zero_le_one N
  have himage : volume ((Subtype.val : s → ℝ) '' A) = 0 := by
    rw [← hausdorffMeasure_real,
      isometry_subtype_coe.hausdorffMeasure_image (Or.inl zero_le_one), hA]
  apply (ae_restrict_iff' hs).mpr
  rw [ae_iff]
  convert himage using 2
  ext t
  simp only [mem_ofPred_eq, not_forall, mem_image, A, N, mem_preimage,
    Set.domRestrict_apply]
  constructor
  · rintro ⟨ht, hQt⟩
    exact ⟨⟨t, ht⟩, hQt, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩

/-- [internal] The AC chain rule for a fixed-density primitive on a monotone
bi-Lipschitz curve. Both inverse Lipschitz bounds are explicit and local to this
interval. The initial density is L¹; no L² bound or continuous outgoing derivative
is assumed. The derivative uses the selected representative on the curve. -/
theorem trace_ac_chain_rule_of_fixedDensity
    {f P R G : ℝ → ℝ → ℂ} {y₀ : ℝ → ℂ} {U V : ℝ → ℝ} {a b : ℝ}
    {KU KV LU LV : ℝ≥0} (hab : a < b)
    (hU : LipschitzOnWith KU U (uIcc a b)) (hV : LipschitzOnWith KV V (uIcc a b))
    (hUm : MonotoneOn U (uIcc a b)) (hVm : MonotoneOn V (uIcc a b))
    (hUa : AntilipschitzWith LU ((uIcc a b).domRestrict U))
    (hVa : AntilipschitzWith LV ((uIcc a b).domRestrict V))
    (hP : ContinuousOn P.uncurry (uIcc (U a) (U b) ×ˢ uIcc (V a) (V b)))
    (hR : ContinuousOn R.uncurry (uIcc (U a) (U b) ×ˢ uIcc (V a) (V b)))
    (hG : ContinuousOn G.uncurry (uIcc (U a) (U b) ×ˢ uIcc (V a) (V b)))
    (hy₀ : IntervalIntegrable y₀ volume (V a) (V b))
    (hin : ∀ u ∈ uIcc (U a) (U b), ∀ v ∈ uIcc (V a) (V b),
      HasDerivWithinAt (fun x => f x v) (G u v) (uIcc (U a) (U b)) u)
    (hrep : ∀ u ∈ uIcc (U a) (U b), ∀ v ∈ uIcc (V a) (V b),
      f u v = f u (V a) + ∫ s in V a..v, fixedDensity P R y₀ u s) :
    AbsolutelyContinuousOnInterval (fun t => f (U t) (V t)) a b ∧
      ∀ᵐ t ∂volume.restrict (uIcc a b),
        HasDerivAt (fun s => f (U s) (V s))
          (deriv U t • G (U t) (V t) + deriv V t • fixedDensity P R y₀ (U t) (V t)) t := by
  have hUab := hUm left_mem_uIcc right_mem_uIcc hab.le
  have hVab := hVm left_mem_uIcc right_mem_uIcc hab.le
  have hP' : ContinuousOn P.uncurry (Icc (U a) (U b) ×ˢ Icc (V a) (V b)) := by
    simpa only [uIcc_of_le hUab, uIcc_of_le hVab] using hP
  have hR' : ContinuousOn R.uncurry (Icc (U a) (U b) ×ˢ Icc (V a) (V b)) := by
    simpa only [uIcc_of_le hUab, uIcc_of_le hVab] using hR
  have hrep' : ∀ u ∈ Icc (U a) (U b), ∀ v ∈ Icc (V a) (V b),
      f u v = f u (V a) + ∫ s in V a..v, fixedDensity P R y₀ u s := by
    simpa only [uIcc_of_le hUab, uIcc_of_le hVab] using hrep
  obtain ⟨C, hC, hbound⟩ := exists_fixedDensity_bound hP' hR'
  obtain ⟨D, hD⟩ := (isCompact_uIcc.prod isCompact_uIcc).exists_bound_of_continuousOn hG
  let M : ℝ≥0 := Real.toNNReal D
  have hLip : ∀ v ∈ uIcc (V a) (V b),
      LipschitzOnWith M (fun u => f u v) (uIcc (U a) (U b)) := by
    intro v hv
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_uIcc _ _)
      (fun u hu => hin u hu v hv)
    intro u hu
    exact_mod_cast (hD (u, v) ⟨hu, hv⟩).trans (Real.le_coe_toNNReal D)
  have hW : ∀ u ∈ uIcc (U a) (U b),
      IntervalIntegrable (fixedDensity P R y₀ u) volume (V a) (V b) := by
    intro u hu
    apply intervalIntegrable_fixedDensity hVab _ hP' hR' hy₀
    rwa [uIcc_of_le hUab] at hu
  have hcontrol : ∀ u ∈ uIcc (U a) (U b), ∀ v ∈ uIcc (V a) (V b),
      ‖fixedDensity P R y₀ u v‖ ≤ C * (‖y₀ v‖ + 1) := by
    intro u hu v hv
    exact hbound y₀ u (by rwa [uIcc_of_le hUab] at hu)
      v (by rwa [uIcc_of_le hVab] at hv)
  refine ⟨absolutelyContinuousOnInterval_trace_of_primitive hU.absolutelyContinuousOnInterval
    hV.absolutelyContinuousOnInterval hUm hVm
    ((hy₀.norm.add intervalIntegrable_const).const_mul C) hLip hW hcontrol hrep, ?_⟩
  have hgood := ae_forall_hasDerivAt_of_fixedDensity_representation hVab hP' hR' hy₀ hrep'
  have hpull := ae_pullback_of_antilipschitzOn measurableSet_uIcc hVa
    ((ae_restrict_iff' measurableSet_Icc).mp hgood)
  have hUS : StrictMonoOn U (uIcc a b) := hUm.strictMonoOn_of_injOn (by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hUa.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
  have hVS : StrictMonoOn V (uIcc a b) := hVm.strictMonoOn_of_injOn (by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hVa.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy))
  have hne (x : ℝ) : ∀ᵐ t ∂volume.restrict (uIcc a b), t ≠ x := by
    apply ae_restrict_of_ae
    simp [ae_iff]
  filter_upwards [hpull, ae_restrict_mem measurableSet_uIcc, hne a, hne b,
    ae_restrict_of_ae hU.absolutelyContinuousOnInterval.ae_differentiableAt,
    ae_restrict_of_ae hV.absolutelyContinuousOnInterval.ae_differentiableAt]
    with t ht htm hta htb hdu hdv
  have hti : t ∈ Ioo a b := by
    rw [uIcc_of_le hab.le] at htm
    exact ⟨lt_of_le_of_ne htm.1 (Ne.symm hta), lt_of_le_of_ne htm.2 htb⟩
  have hui : U t ∈ Ioo (U a) (U b) :=
    ⟨hUS left_mem_uIcc htm hti.1, hUS htm right_mem_uIcc hti.2⟩
  have hvi : V t ∈ Ioo (V a) (V b) :=
    ⟨hVS left_mem_uIcc htm hti.1, hVS htm right_mem_uIcc hti.2⟩
  have hN : uIcc (U a) (U b) ×ˢ uIcc (V a) (V b) ∈ 𝓝 (U t, V t) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hui, hvi⟩] with p hp
    simpa only [uIcc_of_le hUab, uIcc_of_le hVab] using
      (show p ∈ Icc (U a) (U b) ×ˢ Icc (V a) (V b) from
        ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩)
  apply hasDerivAt_trace_of_continuous_incoming_partial (hdu htm).hasDerivAt
    (hdv htm).hasDerivAt (hG.continuousAt hN)
  · filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hui, hvi⟩] with p hp
    have hpu : p.1 ∈ uIcc (U a) (U b) := by
      rw [uIcc_of_le hUab]; exact Ioo_subset_Icc_self hp.1
    have hpv : p.2 ∈ uIcc (V a) (V b) := by
      rw [uIcc_of_le hVab]; exact Ioo_subset_Icc_self hp.2
    exact (hin p.1 hpu p.2 hpv).hasDerivAt (by
      rw [uIcc_of_le hUab]; exact Icc_mem_nhds hp.1.1 hp.1.2)
  · exact ht (Ioo_subset_Icc_self hvi) (U t) (Ioo_subset_Icc_self hui)

end EmcsfAcExtension.Global.Density
