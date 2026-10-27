module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Infra.Level.OrderIso
import EmcsfAcExtension.Global.Terminal.Scalar
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Boundary data in the observation chart

The null chart is recorded by its two inverse coordinate maps. Its diagonal
is the outer cylinder. The formulas below use the original field values and
the actual derivatives of the maps, rather than an `IsSolution` assertion
on a domain with the wrong axis.
Source: charged_SF_new_version.tex:L1980–2034, L2075–2100; internal project record (N).
-/

public section

open Complex Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [internal]
Cylinder inverse maps with the clock rates yield the normalized boundary
values after positive scaling. This helper is the consumer interface for
the cylinder-clock packet; it has no uniform optical bound as a premise. -/
theorem Observation.boundary_null_normalization_of_clock_rates
    (S : Fields) (U V : ℝ → ℝ) {s b t : ℝ} (hs : 0 < s)
    (hU : HasDerivAt U (s / (-2 * S.nu (U t) (V t))) t)
    (hV : HasDerivAt V (s / (2 * S.lam (U t) (V t))) t)
    (hn : S.nu (U t) (V t) < 0) (hl : 0 < S.lam (U t) (V t))
    (hr : S.r (U t) (V t) = b) (hA : S.A (U t) (V t) = 0) :
    let P := nullPullback (rescaleFields S s) (fun x => U x / s) (fun x => V x / s)
    P.r t t = b / s ∧ P.nu t t = -1 / 2 ∧ P.lam t t = 1 / 2 ∧ P.A t t = 0 := by
  have hu := (hU.div_const s).deriv
  have hv := (hV.div_const s).deriv
  have hs0 := hs.ne'
  dsimp only
  simp only [nullPullback, rescaleFields, mul_div_cancel₀ _ hs0, hu, hv, hr, hA, mul_zero]
  refine ⟨trivial, ?_, ?_, trivial⟩
  · field_simp [hs0, hn.ne]
  · field_simp [hs0, hl.ne']

/-- [internal]
Both original coordinate maps of a clock cylinder are strictly increasing
on the proper clock interval. No uniform lower bound on either expansion
is assumed. This supplies their canonical interval inverse labels. -/
theorem Observation.clock_labels_strictMono {e b s t : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (γ : ClockCylinder S D b s t) :
    StrictMonoOn γ.U (Icc s t) ∧ StrictMonoOn γ.V (Icc s t) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc s t) γ.c1_U.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [((γ.rate_U x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
    exact inv_pos.mpr (neg_pos.mpr (hS.nu_neg _ (γ.mem x (Ioo_subset_Icc_self hx))))
  · apply strictMonoOn_of_deriv_pos (convex_Icc s t) γ.c1_V.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [((γ.rate_V x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv]
    exact inv_pos.mpr (hS.lam_pos _ (γ.mem x (Ioo_subset_Icc_self hx)))

/-- [internal]
The normalized outgoing scalar ratio is unchanged by a positive null
Jacobian. The same statement holds for the incoming ratio. -/
theorem Observation.nullPullback_ratios (S : Fields) (U V : ℝ → ℝ)
    {u v du dv : ℝ} (hU : HasDerivAt U du u) (hV : HasDerivAt V dv v)
    (hdu : du ≠ 0) (hdv : dv ≠ 0) :
    (nullPullback S U V).theta u v / (nullPullback S U V).lam u v =
      S.theta (U u) (V v) / S.lam (U u) (V v) ∧
    (nullPullback S U V).xi u v / (nullPullback S U V).nu u v =
      S.xi (U u) (V v) / S.nu (U u) (V v) := by
  have hduC : (du : ℂ) ≠ 0 := by exact_mod_cast hdu
  have hdvC : (dv : ℂ) ≠ 0 := by exact_mod_cast hdv
  simp only [nullPullback, hU.deriv, hV.deriv, Complex.ofReal_mul]
  constructor
  · exact mul_div_mul_left _ _ hdvC
  · exact mul_div_mul_left _ _ hduC

/-- [internal]
An integrated boundary equation is controlled by its squared `L²` density.
The coefficient is the exact interval length, uniformly in the field and
the interval. This applies to the scalar clock equation and Maxwell current. -/
theorem Observation.norm_sub_sq_le_of_integralForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hform : IntegralForm f g a b) (hg : ContinuousOn g (Icc a b)) :
    ‖f b - f a‖ ^ 2 ≤ (b - a) * ∫ x in a..b, ‖g x‖ ^ 2 := by
  have hn : ‖f b - f a‖ ≤ ∫ x in a..b, ‖g x‖ := by
    rw [hform.2]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have hnonneg : 0 ≤ ∫ x in a..b, ‖g x‖ :=
    intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
  have hcs := Terminal.integral_cauchy_schwarz hab hg.norm
    (show ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) from continuousOn_const)
  simp only [mul_one, one_pow, intervalIntegral.integral_const, smul_eq_mul] at hcs
  simpa only [mul_comm] using ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hn).trans hcs

/-- [internal]
The squared increment on any subinterval is bounded by the full window's
length times its squared-density integral. The coefficient is exactly one,
uniformly in the interval, the field and its normed target. -/
theorem Observation.norm_sub_sq_le_window_of_integralForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hg : ContinuousOn g (Icc a b)) (hform : IntegralForm f g s t) :
    ‖f t - f s‖ ^ 2 ≤ (b - a) * ∫ x in a..b, ‖g x‖ ^ 2 := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hi := (hg.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hp (x : ℝ) (_hx : x ∈ Icc a b) : 0 ≤ ‖g x‖ ^ 2 := sq_nonneg _
  have ordered {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d)
      (hf : IntegralForm f g c d) :
      ‖f d - f c‖ ^ 2 ≤ (b - a) * ∫ x in a..b, ‖g x‖ ^ 2 := by
    have hn : 0 ≤ ∫ x in c..d, ‖g x‖ ^ 2 :=
      intervalIntegral.integral_nonneg hcd (fun _ _ => sq_nonneg _)
    have hI := intervalIntegral.integral_mono_interval hc.1 hcd hd.2
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hp x ⟨hx.1.le, hx.2⟩) hi
    have hcs := Observation.norm_sub_sq_le_of_integralForm hcd hf
      (hg.mono (Icc_subset_Icc hc.1 hd.2))
    exact hcs.trans (mul_le_mul (by linarith only [hc.1, hd.2]) hI hn (sub_nonneg.mpr hab))
  rcases le_total s t with hst | hts
  · exact ordered hs ht hst hform
  · simpa only [norm_sub_rev] using ordered ht hs hts hform.symm

/-- [internal]
A bounded ordinary variation bounds oscillation from any point in its set.
No absolute-continuity hypothesis is needed for this exact coefficient-one
bound, and the variation may be supplied by the parallel-frame identity. -/
theorem Observation.norm_sub_le_of_variation_bound {f : ℝ → ℂ} {s : Set ℝ}
    {x y V : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hV0 : 0 ≤ V)
    (hV : eVariationOn f s ≤ ENNReal.ofReal V) : ‖f x - f y‖ ≤ V := by
  have he := (eVariationOn.edist_le f hx hy).trans hV
  rw [edist_dist, dist_eq_norm] at he
  exact (ENNReal.ofReal_le_ofReal_iff hV0).mp he

/-- [internal]
Failure of observation bounds the unnormalized energy by the square of the
enlarged scale. The coefficient four is universal. This is the algebraic
normalization step in internal project record, quantifier closure. -/
theorem Observation.failed_observation_error_of_scale {b m C E : ℝ} (y : ℂ)
    (hb : 0 < b) (hm : 0 ≤ m) (hC : 0 < C)
    (hfailure : C * E < b * (‖y‖ ^ 2 + (2 * m / b) ^ 2)) :
    E < 4 * (m + b * ‖y‖) ^ 2 / (b * C) := by
  have hscale : b * (‖y‖ ^ 2 + (2 * m / b) ^ 2) ≤ 4 * (m + b * ‖y‖) ^ 2 / b := by
    apply (le_div_iff₀ hb).mpr
    have he : b * (‖y‖ ^ 2 + (2 * m / b) ^ 2) * b = b ^ 2 * ‖y‖ ^ 2 + 4 * m ^ 2 := by
      field_simp
      ring
    rw [he]
    nlinarith only [mul_nonneg hm (mul_nonneg hb.le (norm_nonneg y)), sq_nonneg (b * ‖y‖)]
  apply (lt_div_iff₀ (mul_pos hb hC)).mpr
  have he := (mul_lt_mul_of_pos_right (hfailure.trans_le hscale) hb)
  rw [div_mul_cancel₀ _ hb.ne'] at he
  nlinarith only [he]

/-- [internal]
Uniform oscillation and measured `L²` error give the incoming boundary
error. The coefficients `4T` and `2` are explicit and independent of all
fields, the scalar background, coupling and normalized outer radius. -/
theorem Observation.incoming_boundary_l2_of_error_budget
    {T L V D : ℝ} (a q : ℝ → ℂ) (H : ℂ) (hT : 0 ≤ T) (hL : 0 < L)
    (ha : ContinuousOn a (Icc (-T * L) (T * L)))
    (hq : ContinuousOn q (Icc (-T * L) (T * L)))
    (hV : ∀ t ∈ Icc (-T * L) (T * L), ‖a t - H‖ ≤ V)
    (hV0 : 0 ≤ V) (hD : (∫ t in (-T * L)..(T * L), ‖q t‖ ^ 2) ≤ D) :
    (∫ t in (-T * L)..(T * L), ‖a t - H - q t‖ ^ 2) ≤ 4 * T * L * V ^ 2 + 2 * D := by
  have hab : -T * L ≤ T * L := by nlinarith only [mul_nonneg hT hL.le]
  have hac : ContinuousOn (fun t => a t - H) (Icc (-T * L) (T * L)) :=
    ha.sub continuousOn_const
  have iq := (hq.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have ie := ((hac.sub hq).norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hp (t : ℝ) (ht : t ∈ Icc (-T * L) (T * L)) :
      ‖a t - H - q t‖ ^ 2 ≤ 2 * V ^ 2 + 2 * ‖q t‖ ^ 2 := by
    have hn := norm_sub_le (a t - H) (q t)
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
    have hv := (sq_le_sq₀ (norm_nonneg _) hV0).mpr (hV t ht)
    nlinarith only [hs, hv, sq_nonneg (‖a t - H‖ - ‖q t‖)]
  have hi := intervalIntegral.integral_mono_on hab ie
    ((intervalIntegrable_const (c := 2 * V ^ 2)).add (iq.const_mul 2)) hp
  rw [intervalIntegral.integral_add intervalIntegrable_const (iq.const_mul 2),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul, Pi.pow_apply, Pi.sub_apply] at hi
  linarith

/-- [internal]
For every fixed window parameter and requested positive error, an explicit
observation constant turns the normalized variation and dissipation budgets
into both small-boundary inequalities. The constant depends only on `T`
and `ε`, before the fields, background and radius are quantified. -/
theorem co_small_boundary_of_normalized_error_budget {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L V : ℝ) (a q : ℝ → ℂ) (H : ℂ), 0 < L → 0 ≤ V →
        ContinuousOn a (Icc (-T * L) (T * L)) →
        ContinuousOn q (Icc (-T * L) (T * L)) → a 0 = H →
        eVariationOn a (Icc (-T * L) (T * L)) ≤ ENNReal.ofReal V →
        V ^ 2 ≤ 4 / (L ^ 2 * C) →
        (∫ t in (-T * L)..(T * L), ‖q t‖ ^ 2) ≤ 8 / (L * C) →
        (∀ t ∈ Icc (-T * L) (T * L), ‖a t - H‖ ≤ ε / L) ∧
        (∫ t in (-T * L)..(T * L), ‖a t - H - q t‖ ^ 2) ≤ ε ^ 2 / L := by
  let C := 16 * (T + 1) / ε ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro L V a q H hL hV0 ha hq hH hvar hV hQ
  have hzero : (0 : ℝ) ∈ Icc (-T * L) (T * L) :=
    ⟨by nlinarith only [mul_nonneg hT hL.le], mul_nonneg hT hL.le⟩
  have hosc (t : ℝ) (ht : t ∈ Icc (-T * L) (T * L)) : ‖a t - H‖ ≤ V := by
    rw [← hH]
    exact Observation.norm_sub_le_of_variation_bound ht hzero hV0 hvar
  have hcoef : 4 / (L ^ 2 * C) ≤ (ε / L) ^ 2 := by
    dsimp [C]
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hL) hC)).mpr
    have he : (ε / L) ^ 2 * (L ^ 2 * (16 * (T + 1) / ε ^ 2)) = 16 * (T + 1) := by
      field_simp
    rw [he]
    linarith
  have hvε : V ≤ ε / L := (sq_le_sq₀ hV0 (div_pos hε hL).le).mp (hV.trans hcoef)
  refine ⟨fun t ht => (hosc t ht).trans hvε, ?_⟩
  have he := Observation.incoming_boundary_l2_of_error_budget a q H hT hL ha hq hosc hV0 hQ
  have hmul := mul_le_mul_of_nonneg_left hV (show 0 ≤ 4 * T * L by positivity)
  have hid : 4 * T * L * (4 / (L ^ 2 * C)) + 2 * (8 / (L * C)) = ε ^ 2 / L := by
    dsimp [C]
    field_simp
    ring
  exact he.trans (hid ▸ add_le_add_left hmul (2 * (8 / (L * C))))

/-- [internal]
Failure of observation gives the two normalized error budgets, including
the exact factor `2/s` from the boundary clock. Enlarging the physical
scale is harmless. All numerical coefficients are universal. -/
theorem Observation.normalized_error_budget_of_failed_observation
    {b m s C I V : ℝ} (y : ℂ) (hb : 0 < b) (hm : 0 ≤ m) (hs : 0 < s)
    (hC : 0 < C) (hI : 0 ≤ I) (hscale : m + b * ‖y‖ ≤ s)
    (hfailure : C * (I + b * V ^ 2) < b * (‖y‖ ^ 2 + (2 * m / b) ^ 2)) :
    V ^ 2 ≤ 4 / ((b / s) ^ 2 * C) ∧ (2 / s) * I ≤ 8 / ((b / s) * C) := by
  have hE := Observation.failed_observation_error_of_scale y hb hm hC hfailure
  have hsq := (sq_le_sq₀ (add_nonneg hm (mul_nonneg hb.le (norm_nonneg y))) hs.le).mpr hscale
  have hE' : I + b * V ^ 2 ≤ 4 * s ^ 2 / (b * C) :=
    hE.le.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num)) (mul_nonneg hb.le hC.le))
  constructor
  · calc
      _ ≤ (I + b * V ^ 2) / b := (le_div_iff₀ hb).mpr (by nlinarith only [hI])
      _ ≤ (4 * s ^ 2 / (b * C)) / b := div_le_div_of_nonneg_right hE' hb.le
      _ = _ := by field_simp
  · calc
      _ ≤ (2 / s) * (I + b * V ^ 2) := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg hb.le (sq_nonneg V))) (by positivity)
      _ ≤ (2 / s) * (4 * s ^ 2 / (b * C)) := mul_le_mul_of_nonneg_left hE' (by positivity)
      _ = _ := by field_simp; norm_num

/-- [node eq:co-small-boundary]
For each fixed window and requested error, failed physical observation
implies both normalized small-boundary estimates. The trace is pulled back
by the actual affine clock, and its `L²` measure factor and variation are
proved here. `C` depends only on `T` and `ε`, uniformly in all physical
data, the positive normalizing scale and the retained scalar background. -/
theorem co_small_boundary_of_failed_observation {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b m s τ₀ V : ℝ) (y H : ℂ) (a q : ℝ → ℂ),
        0 < b → 0 ≤ m → 0 < s → 0 ≤ V → m + b * ‖y‖ ≤ s →
        ContinuousOn a (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) →
        ContinuousOn q (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) → a τ₀ = H →
        eVariationOn a (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ≤ ENNReal.ofReal V →
        C * ((∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2) + b * V ^ 2) <
          b * (‖y‖ ^ 2 + (2 * m / b) ^ 2) →
        (∀ t ∈ Icc (-T * (b / s)) (T * (b / s)),
          ‖a (τ₀ + (s / 2) * t) - H‖ ≤ ε / (b / s)) ∧
        (∫ t in (-T * (b / s))..(T * (b / s)),
          ‖a (τ₀ + (s / 2) * t) - H - q (τ₀ + (s / 2) * t)‖ ^ 2) ≤ ε ^ 2 / (b / s) := by
  obtain ⟨C, hC, hprop⟩ := co_small_boundary_of_normalized_error_budget hT hε
  refine ⟨C, hC, ?_⟩
  intro b m s τ₀ V y H a q hb hm hs hV0 hscale ha hq ha0 hvar hfailure
  let L := b / s
  let f : ℝ → ℝ := fun t => τ₀ + (s / 2) * t
  have hL : 0 < L := div_pos hb hs
  have hab : -T * L ≤ T * L := by nlinarith only [mul_nonneg hT hL.le]
  have hf : Continuous f := by fun_prop
  have hmono : Monotone f := by
    intro x z hxz
    dsimp [f]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hxz (by positivity)) τ₀
  have hfa : f (-T * L) = τ₀ - T * b / 2 := by dsimp [f, L]; field_simp; ring
  have hfb : f (T * L) = τ₀ + T * b / 2 := by dsimp [f, L]; field_simp
  have himage : f '' Icc (-T * L) (T * L) = Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    simpa only [hfa, hfb] using hf.continuousOn.image_Icc_of_monotoneOn hab (hmono.monotoneOn _)
  have hmap : MapsTo f (Icc (-T * L) (T * L)) (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) := by
    rw [← himage]
    exact mapsTo_image f _
  have hveq : eVariationOn (fun t => a (f t)) (Icc (-T * L) (T * L)) =
      eVariationOn a (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) := by
    change eVariationOn (a ∘ f) _ = _
    rw [eVariationOn.comp_eq_of_monotoneOn a f (hmono.monotoneOn _), himage]
  have htime :
      (∫ t in (-T * L)..(T * L), ‖q (f t)‖ ^ 2) =
        (2 / s) * ∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2 := by
    have he := intervalIntegral.integral_comp_add_mul (fun τ => ‖q τ‖ ^ 2)
      (a := -T * L) (b := T * L) (c := s / 2) (by positivity) τ₀
    change (∫ t in (-T * L)..(T * L), ‖q (f t)‖ ^ 2) =
      (s / 2)⁻¹ • ∫ τ in (f (-T * L))..(f (T * L)), ‖q τ‖ ^ 2 at he
    rw [hfa, hfb] at he
    simpa only [smul_eq_mul, inv_div] using! he
  have hI : 0 ≤ ∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by nlinarith only [mul_nonneg hT hb.le])
      (fun _ _ => sq_nonneg _)
  obtain ⟨hV, hQ⟩ := Observation.normalized_error_budget_of_failed_observation
    y hb hm hs hC hI hscale hfailure
  apply hprop L V (fun t => a (f t)) (fun t => q (f t)) H hL hV0
    (ha.comp hf.continuousOn hmap) (hq.comp hf.continuousOn hmap)
  · simpa [f] using ha0
  · rw [hveq]
    exact hvar
  · exact hV
  · rw [htime]
    exact hQ

/-- [internal]
Continuous boundary tangent equations give integral equations on every
subinterval, including the window endpoints. Derivatives are needed only
in the interior. This is the FTC interface for the internal project record tangent helpers. -/
theorem Observation.integralForm_on_of_continuous_tangent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, IntegralForm f g s t := by
  have ordered {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      IntegralForm f g s t := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hi := (hg.mono hsub).intervalIntegrable_of_Icc (μ := volume) hst
    refine ⟨hi, ?_⟩
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hf.mono hsub)
      (fun x hx => hd x ⟨hs.1.trans_lt hx.1, hx.2.trans_le ht.2⟩) hi).symm
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact ordered hs ht hst
  · exact (ordered ht hs hts).symm

end EmcsfAcExtension.Global
