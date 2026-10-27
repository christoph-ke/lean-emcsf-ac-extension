module

public import EmcsfAcExtension.Infra.AC.Primitive
public import EmcsfAcExtension.Frozen.Triangle
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.UniformSpace.UniformConvergence
import EmcsfAcExtension.Local.Stability.GeomStrongValueLimit
import EmcsfAcExtension.Local.Stability.GeomStrongACSections
import EmcsfAcExtension.Infra.Mixed.SupSum
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Local.Stability.GeomStrongCauchy

/-! # Strong real characteristic derivatives through prescribed uniform limits

Uniform completeness identifies the ordinary derivative of the prescribed
primitive. Variation semicontinuity then passes pair bounds with coefficient
one, including the sum of the two section suprema.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- For real AC curves the derivative difference norm is exactly the variation
of their difference. The coefficient is one, uniformly in endpoints and curves. -/
theorem real_variation_sub_eq_lintegral {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    eVariationOn (f - g) (Icc a b) = ∫⁻ x in Icc a b, ‖deriv f x - deriv g x‖ₑ := by
  have hi := hf.intervalIntegrable_deriv.sub hg.intervalIntegrable_deriv
  rw [(hf.sub hg).eVariationOn_eq_integral_norm_deriv hab,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have he : deriv (f - g) =ᵐ[volume.restrict (Icc a b)] fun x => deriv f x - deriv g x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hf.ae_differentiableAt,
      ae_restrict_of_ae hg.ae_differentiableAt] with x hx hfx hgx
    exact ((hfx (Icc_subset_uIcc hx)).hasDerivAt.sub
      (hgx (Icc_subset_uIcc hx)).hasDerivAt).deriv
  have he' := he.fun_comp norm
  simp only [Function.comp_def] at he'
  rw [integral_congr_ae he']
  exact ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hi)

/-- A prescribed real uniform limit of AC section families with uniformly
Cauchy ordinary derivatives is AC and has section-uniform strong derivatives.
All error coefficients are one; no interval or density bound is assumed. -/
theorem real_ac_family_strong_of_uniform_cauchy {ι : Type*}
    {a b : ι → ℝ} {F : ℕ → ι → ℝ → ℝ} {f : ι → ℝ → ℝ}
    (hab : ∀ i, a i ≤ b i)
    (hF : ∀ n i, AbsolutelyContinuousOnInterval (F n i) (a i) (b i))
    (hl : TendstoUniformlyOn (fun n (p : ι × ℝ) => F n p.1 p.2)
      (fun p => f p.1 p.2) atTop {p | p.2 ∈ Icc (a p.1) (b p.1)})
    (hc : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, ∀ i,
      (∫⁻ x in Icc (a i) (b i), ‖deriv (F n i) x - deriv (F m i) x‖ₑ) < ENNReal.ofReal ρ) :
    (∀ i, AbsolutelyContinuousOnInterval (f i) (a i) (b i)) ∧
      (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ i,
        (∫ x in a i..b i, ‖deriv (F n i) x - deriv (f i) x‖) < ρ) := by
  obtain ⟨q, hq, hstrong, hac, hprim⟩ := stab_real_ac_limit_of_uniform_and_density_cauchy hab
    (fun n i => (stab_real_ac_section_primitive (hab i) (hF n i)).1) hc
    (fun n i => (stab_real_ac_section_primitive (hab i) (hF n i)).2) (by
      intro ρ hρ
      obtain ⟨N,hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hl) ρ hρ)
      exact ⟨N, fun n hn i x hx => by
        simpa only [Real.dist_eq, abs_sub_comm] using hN n hn (i,x) hx⟩)
  have hd i : deriv (f i) =ᵐ[volume.restrict (Icc (a i) (b i))] q i := by
    have hi : IntervalIntegrable (q i) volume (a i) (b i) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (hab i)).2 (hq i)
    have hne (z : ℝ) : ∀ᵐ x : ℝ, x ≠ z := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hi.ae_hasDerivAt_integral,
      ae_restrict_of_ae (hne (a i)), ae_restrict_of_ae (hne (b i))] with x hx hdx hxa hxb
    have hn := Icc_mem_nhds (lt_of_le_of_ne hx.1 hxa.symm) (lt_of_le_of_ne hx.2 hxb)
    have he : f i =ᶠ[𝓝 x] fun x => f i (a i) + ∫ t in a i..x, q i t :=
      Filter.eventuallyEq_of_mem hn (hprim i)
    exact he.deriv_eq.trans ((hdx (Icc_subset_uIcc hx) (a i) left_mem_uIcc).const_add _).deriv
  refine ⟨hac, ?_⟩
  intro ρ hρ
  obtain ⟨N,hN⟩ := hstrong ρ hρ
  refine ⟨N, fun n hn i => ?_⟩
  rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
  have he : (fun x => ‖deriv (F n i) x - deriv (f i) x‖) =ᵐ[volume.restrict (Icc (a i) (b i))]
      fun x => |deriv (F n i) x - q i x| := by
    filter_upwards [hd i] with x hx
    rw [hx, Real.norm_eq_abs]
  rw [integral_congr_ae he]
  exact hN n hn i

/-- Pass the sum of both ordinary derivative section suprema through pointwise
limits of AC pairs. Every bound and dimensional factor is retained unchanged;
AC of the limiting pair must first be established by completeness. -/
theorem real_characteristic_pair_of_pointwise {T : ℝ}
    {F G : ℕ → ℝ → ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {L : ℕ → ℝ≥0∞} {l : ℝ≥0∞}
    (hFo : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval (F n u) u T)
    (hGo : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval (G n u) u T)
    (hFi : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => F n u v) 0 v)
    (hGi : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => G n u v) 0 v)
    (hfo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T)
    (hgo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (g u) u T)
    (hfi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v)
    (hgi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => g u v) 0 v)
    (hF : ∀ p ∈ triangle 0 T, Tendsto (fun n => F n p.1 p.2) atTop (𝓝 (f p.1 p.2)))
    (hG : ∀ p ∈ triangle 0 T, Tendsto (fun n => G n p.1 p.2) atTop (𝓝 (g p.1 p.2)))
    (hL : Tendsto L atTop (𝓝 l))
    (hb : ∀ n,
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (F n u) v - deriv (G n u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => F n s v) u - deriv (fun s => G n s v) u‖ₑ) ≤ L n) :
    (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (f u) v - deriv (g u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => f s v) u - deriv (fun s => g s v) u‖ₑ) ≤ l := by
  have heo n (u : Icc (0 : ℝ) T) :=
    real_variation_sub_eq_lintegral u.property.2 (hFo n u u.property) (hGo n u u.property)
  have hei n (v : Icc (0 : ℝ) T) :=
    real_variation_sub_eq_lintegral v.property.1 (hFi n v v.property) (hGi n v v.property)
  have helo (u : Icc (0 : ℝ) T) :=
    real_variation_sub_eq_lintegral u.property.2 (hfo u u.property) (hgo u u.property)
  have heli (v : Icc (0 : ℝ) T) :=
    real_variation_sub_eq_lintegral v.property.1 (hfi v v.property) (hgi v v.property)
  have h := Mixed.iSup_eVariationOn_add_le_of_tendsto
    (F := fun n (u : Icc (0 : ℝ) T) => F n u - G n u)
    (G := fun n (v : Icc (0 : ℝ) T) => (fun u => F n u v) - (fun u => G n u v))
    (f := fun (u : Icc (0 : ℝ) T) => f u - g u)
    (g := fun (v : Icc (0 : ℝ) T) => (fun u => f u v) - (fun u => g u v))
    (s := fun u => Icc (u : ℝ) T) (t := fun v => Icc 0 (v : ℝ))
    (fun u v hv => (hF (u,v) ⟨u.property.1,hv.1,hv.2⟩).sub (hG (u,v) ⟨u.property.1,hv.1,hv.2⟩))
    (fun v u hu => (hF (u,v) ⟨hu.1,hu.2,v.property.2⟩).sub (hG (u,v) ⟨hu.1,hu.2,v.property.2⟩))
    hL (Eventually.of_forall fun n => by
      simpa only [heo, hei, iSup_subtype] using hb n)
  simpa only [helo, heli, iSup_subtype] using h

/-- AC and strong ordinary derivative convergence of a real field on both
complete families of characteristic sections. Uniform convergence includes
all axis endpoints; the strong convergence index is uniform in the label. -/
structure RealCharacteristicLimit (T : ℝ) (Fn : ℕ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop where
  /-- Every original outgoing section is AC. -/
  ac_out : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval (Fn n u) u T
  /-- Every original incoming section is AC. -/
  ac_in : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => Fn n u v) 0 v
  /-- Every limiting outgoing section is AC. -/
  limit_ac_out : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T
  /-- Every limiting incoming section is AC. -/
  limit_ac_in : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v
  /-- Uniform values on the entire closed triangle. -/
  uniform : TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop
      (triangle 0 T)
  /-- Strong outgoing derivatives uniformly in the section label. -/
  strong_out : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
    (∫ v in u..T, ‖deriv (Fn n u) v - deriv (f u) v‖) < ρ
  /-- Strong incoming derivatives uniformly in the section label. -/
  strong_in : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
    (∫ u in (0 : ℝ)..v, ‖deriv (fun s => Fn n s v) u - deriv (fun s => f s v) u‖) < ρ

/-- Uniform AC completeness for a real characteristic field with a common
pair bound. `K` may be any fixed nonnegative number for this family, including
zero. Its full dimensional dependence is retained by the caller. -/
theorem real_characteristic_limit_of_pair_bound {T K : ℝ}
    {Fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {d : ℕ → ℕ → ℝ}
    (hK : 0 ≤ K) (hd0 : ∀ n m, 0 ≤ d n m)
    (ho : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval (Fn n u) u T)
    (hi : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => Fn n u v) 0 v)
    (hl : TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop (triangle
        0 T))
    (hd : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d n m < ρ)
    (hb : ∀ n m,
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (Fn n u) v - deriv (Fn m u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => Fn n s v) u - deriv (fun s => Fn m s v) u‖ₑ) ≤
          ENNReal.ofReal (K * d n m)) : RealCharacteristicLimit T Fn f := by
  have hK' : 0 < K + 1 := by linarith
  have hbo n m : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (Fn n u) v - deriv (Fn m u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => Fn n s v) u - deriv (fun s => Fn m s v) u‖ₑ) ≤
          ENNReal.ofReal ((K+1) * d n m) :=
    (hb n m).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (hd0 n m)))
  let I := Icc (0 : ℝ) T
  have co := stab_uniform_cauchy_of_pair_bound hK' hd (fun n m (u : I) =>
    (le_iSup₂ u.val u.property).trans (le_self_add.trans (hbo n m)))
  have ci := stab_uniform_cauchy_of_pair_bound hK' hd (fun n m (v : I) =>
    (le_iSup₂ v.val v.property).trans (le_add_self.trans (hbo n m)))
  obtain ⟨hao,hso⟩ := real_ac_family_strong_of_uniform_cauchy
    (a := fun u : I => u.val) (b := fun _ => T)
    (F := fun n (u : I) => Fn n u) (f := fun (u : I) => f u)
    (fun u => u.property.2) (fun n u => ho n u u.property)
    ((hl.comp (fun p : I × ℝ => (p.1.val,p.2))).mono
      (fun p hp => ⟨p.1.property.1,hp.1,hp.2⟩)) co
  obtain ⟨hai,hsi⟩ := real_ac_family_strong_of_uniform_cauchy
    (a := fun _ : I => (0 : ℝ)) (b := fun v => v.val)
    (F := fun n (v : I) u => Fn n u v) (f := fun (v : I) u => f u v)
    (fun v => v.property.1) (fun n v => hi n v v.property)
    ((hl.comp (fun p : I × ℝ => (p.2,p.1.val))).mono
      (fun p hp => ⟨hp.1,hp.2,p.1.property.2⟩)) ci
  refine ⟨ho,hi,fun u hu => hao ⟨u,hu⟩,fun v hv => hai ⟨v,hv⟩,hl,?_,?_⟩
  · intro ρ hρ
    obtain ⟨N,hN⟩ := hso ρ hρ
    exact ⟨N,fun n hn u hu => hN n hn ⟨u,hu⟩⟩
  · intro ρ hρ
    obtain ⟨N,hN⟩ := hsi ρ hρ
    exact ⟨N,fun n hn v hv => hN n hn ⟨v,hv⟩⟩

/-- A real pair supremum estimate and Cauchy data upgrade pointwise convergence
to uniform convergence. The fixed coefficient is chosen before section labels;
this helper does not infer any derivative convergence from uniform values. -/
theorem real_uniform_of_pair_bound {D : Set (ℝ × ℝ)} {K : ℝ}
    {Fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {d : ℕ → ℕ → ℝ}
    (hK : 0 < K)
    (hd : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, d n m < ρ)
    (hb : ∀ n m p, p ∈ D → |Fn n p.1 p.2 - Fn m p.1 p.2| ≤ K * d n m)
    (hp : ∀ p ∈ D, Tendsto (fun n => Fn n p.1 p.2) atTop (𝓝 (f p.1 p.2))) :
    TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop D := by
  have hc : UniformCauchySeqOn (fun n => Function.uncurry (Fn n)) atTop D := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ρ hρ
    obtain ⟨N,hN⟩ := hd (ρ / K) (div_pos hρ hK)
    refine ⟨N,fun n hn m hm p hp => ?_⟩
    rw [Real.dist_eq]
    exact (hb n m p hp).trans_lt ((lt_div_iff₀' hK).1 (hN n hn m hm))
  exact hc.tendstoUniformlyOn_of_tendsto hp

/-- Convert a finite nonnegative derivative L¹ bound to the real interval
integral on an ordered AC section. All conversion coefficients are one. -/
theorem real_derivative_integral_le {f g : ℝ → ℝ} {a b D : ℝ}
    (hab : a ≤ b) (hD : 0 ≤ D)
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hb : (∫⁻ x in Icc a b, ‖deriv f x - deriv g x‖ₑ) ≤ ENNReal.ofReal D) :
    (∫ x in a..b, ‖deriv f x - deriv g x‖) ≤ D := by
  apply (ENNReal.ofReal_le_ofReal_iff hD).1
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_norm_eq_lintegral_enorm
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
        (hf.intervalIntegrable_deriv.sub hg.intervalIntegrable_deriv))]
  exact hb

/-- A derivative comparison with a vanishing nonnegative error gives both
section-uniform strong limits on an already identified AC field. The fixed
coefficient `K` retains all of its explicit dimensional dependence. -/
theorem real_characteristic_limit_of_vanishing_bound {T K : ℝ}
    {Fn : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {d : ℕ → ℝ}
    (hK : 0 ≤ K) (hd0 : ∀ n, 0 ≤ d n)
    (ho : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval (Fn n u) u T)
    (hi : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => Fn n u v) 0 v)
    (hfo : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (f u) u T)
    (hfi : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => f u v) 0 v)
    (hl : TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop (triangle
        0 T))
    (hd : Tendsto d atTop (𝓝 0))
    (hb : ∀ n,
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (Fn n u) v - deriv (f u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => Fn n s v) u - deriv (fun s => f s v) u‖ₑ) ≤ ENNReal.ofReal (K * d n)) :
    RealCharacteristicLimit T Fn f := by
  have ht : Tendsto (fun n => K * d n) atTop (𝓝 0) := by simpa using hd.const_mul K
  refine ⟨ho,hi,hfo,hfi,hl,?_,?_⟩
  · intro ρ hρ
    obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 ρ hρ)
    exact ⟨N,fun n hn u hu => (real_derivative_integral_le hu.2 (mul_nonneg hK (hd0 n))
      (ho n u hu) (hfo u hu) ((le_iSup₂ u hu).trans (le_self_add.trans (hb n)))).trans_lt (hN n hn)⟩
  · intro ρ hρ
    obtain ⟨N,hN⟩ := eventually_atTop.1 ((tendsto_order.1 ht).2 ρ hρ)
    exact ⟨N,fun n hn v hv => (real_derivative_integral_le hv.1 (mul_nonneg hK (hd0 n))
      (hi n v hv) (hfi v hv) ((le_iSup₂ v hv).trans (le_add_self.trans (hb n)))).trans_lt (hN n hn)⟩

end EmcsfAcExtension.Local
