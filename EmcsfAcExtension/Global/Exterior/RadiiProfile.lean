module

public import Mathlib

/-! # Dyadic radii and the one-sided adaptive radius majorant

The moving supremum in `charged_SF_new_version.tex:L1107–L1138` preserves monotonicity
and gives the prescribed Lipschitz bound, including at jumps of the step
profile. The estimates below do not require the supremum to be attained.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [def-node c:exterior#lipschitz-radius-majorant]
The literal one-sided supremum from `charged_SF_new_version.tex:L1108–L1111`.
Its properties are used only on `0 < x ≤ R₀`. -/
@[expose] noncomputable def radiusMajorant (h : ℝ → ℝ) (R₀ k x : ℝ) : ℝ :=
  sSup ((fun s => h s - k * (s - x)) '' Icc x R₀)

private theorem candidate_bdd {h : ℝ → ℝ} {R₀ k x : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Ioc 0 R₀)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    BddAbove ((fun s => h s - k * (s - x)) '' Icc x R₀) := by
  refine ⟨k / 2 * x, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have hh' := hh s ⟨hx.1.trans_le hs.1, hs.2⟩
  have hp := mul_nonneg hk (sub_nonneg.mpr hs.1)
  linarith

/-- [internal]
The majorant dominates its profile, without continuity or attainment.
The only constant is the prescribed numerical slope `k`. -/
theorem le_radiusMajorant {h : ℝ → ℝ} {R₀ k x : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Ioc 0 R₀)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    h x ≤ radiusMajorant h R₀ k x := by
  have hm : h x ∈ ((fun s => h s - k * (s - x)) '' Icc x R₀) := by
    exact ⟨x, ⟨le_rfl, hx.2⟩, by simp⟩
  exact le_csSup (candidate_bdd hk hx hh) hm

/-- [internal]
The source profile bound is inherited by its majorant. This also supplies
the upper bound required for every subsequent supremum argument. -/
theorem radiusMajorant_le {h : ℝ → ℝ} {R₀ k x : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Ioc 0 R₀)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    radiusMajorant h R₀ k x ≤ k / 2 * x := by
  unfold radiusMajorant
  have hne : ((fun s => h s - k * (s - x)) '' Icc x R₀).Nonempty :=
    ⟨h x, x, ⟨le_rfl, hx.2⟩, by simp⟩
  apply csSup_le hne
  rintro _ ⟨s, hs, rfl⟩
  have hh' := hh s ⟨hx.1.trans_le hs.1, hs.2⟩
  have hp := mul_nonneg hk (sub_nonneg.mpr hs.1)
  linarith

/-- [internal]
Comparison of the two moving index sets proves monotonicity, including
across every jump of the step radius (`charged_SF_new_version.tex:L1072`). -/
theorem radiusMajorant_monotoneOn {h : ℝ → ℝ} {R₀ k : ℝ}
    (hk : 0 ≤ k) (hm : MonotoneOn h (Ioc 0 R₀))
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    MonotoneOn (radiusMajorant h R₀ k) (Ioc 0 R₀) := by
  intro x hx y hy hxy
  unfold radiusMajorant
  have hne : ((fun s => h s - k * (s - x)) '' Icc x R₀).Nonempty :=
    ⟨h x, x, ⟨le_rfl, hx.2⟩, by simp⟩
  apply csSup_le hne
  rintro _ ⟨s, hs, rfl⟩
  by_cases hys : y ≤ s
  · have hc := le_csSup (candidate_bdd hk hy hh)
      (mem_image_of_mem (fun s => h s - k * (s - y)) ⟨hys, hs.2⟩)
    have hp := mul_nonneg hk (sub_nonneg.mpr hxy)
    linarith
  · calc
      h s - k * (s - x) ≤ h s := sub_le_self _ (mul_nonneg hk (sub_nonneg.mpr hs.1))
      _ ≤ h y := hm ⟨hx.1.trans_le hs.1, hs.2⟩ hy (le_of_not_ge hys)
      _ ≤ radiusMajorant h R₀ k y := le_radiusMajorant hk hy hh

private theorem radiusMajorant_sub_le {h : ℝ → ℝ} {R₀ k x y : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Ioc 0 R₀) (hy : y ∈ Ioc 0 R₀) (hxy : x ≤ y)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    radiusMajorant h R₀ k y - radiusMajorant h R₀ k x ≤ k * (y - x) := by
  suffices radiusMajorant h R₀ k y ≤ radiusMajorant h R₀ k x + k * (y - x) by
    linarith
  unfold radiusMajorant
  have hne : ((fun s => h s - k * (s - y)) '' Icc y R₀).Nonempty :=
    ⟨h y, y, ⟨le_rfl, hy.2⟩, by simp⟩
  apply csSup_le hne
  rintro _ ⟨s, hs, rfl⟩
  have hc := le_csSup (candidate_bdd hk hx hh)
    (mem_image_of_mem (fun s => h s - k * (s - x)) ⟨hxy.trans hs.1, hs.2⟩)
  linarith

/-- [internal]
The moving supremum is `k`-Lipschitz. The constant is exactly the freely
prescribed slope, independent of the profile and the outer radius. -/
theorem radiusMajorant_lipschitzOnWith {h : ℝ → ℝ} {R₀ k : ℝ}
    (hk : 0 ≤ k) (hm : MonotoneOn h (Ioc 0 R₀))
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s) :
    LipschitzOnWith (Real.toNNReal k) (radiusMajorant h R₀ k) (Ioc 0 R₀) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rw [Real.coe_toNNReal _ hk]
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr
      (radiusMajorant_monotoneOn hk hm hh hx hy hxy)), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hb := radiusMajorant_sub_le hk hx hy hxy hh
    linarith
  · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
      (radiusMajorant_monotoneOn hk hm hh hy hx hyx)), Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact radiusMajorant_sub_le hk hy hx hyx hh

/-- [internal]
Only candidates with `s < 2x` can be positive. This is the localization
that transfers the little-o property to the moving supremum. -/
theorem radiusMajorant_local_bound {h : ℝ → ℝ} {R₀ k x η : ℝ}
    (hk : 0 ≤ k) (hx : x ∈ Ioc 0 R₀) (hη : 0 ≤ η)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s)
    (hloc : ∀ s ∈ Ioc 0 R₀, s < 2 * x → h s ≤ η / 2 * s) :
    radiusMajorant h R₀ k x ≤ η * x := by
  unfold radiusMajorant
  have hne : ((fun s => h s - k * (s - x)) '' Icc x R₀).Nonempty :=
    ⟨h x, x, ⟨le_rfl, hx.2⟩, by simp⟩
  apply csSup_le hne
  rintro _ ⟨s, hs, rfl⟩
  have hs' : s ∈ Ioc 0 R₀ := ⟨hx.1.trans_le hs.1, hs.2⟩
  by_cases hsx : s < 2 * x
  · have hb := hloc s hs' hsx
    have hp := mul_nonneg hk (sub_nonneg.mpr hs.1)
    have he := mul_nonneg hη (sub_nonneg.mpr hsx.le)
    linarith
  · have hb := hh s hs'
    have hp := mul_nonneg hk (sub_nonneg.mpr (le_of_not_gt hsx))
    have he := mul_nonneg hη hx.1.le
    linarith

/-- [internal]
The majorant is little-o of the radius if the positive profile is.
The proof localizes positive candidates to `[x,2x)`; it uses no regularity
of the profile at the dyadic jump points. -/
theorem radiusMajorant_tendsto_div {h : ℝ → ℝ} {R₀ k : ℝ}
    (hR : 0 < R₀) (hk : 0 ≤ k)
    (hp : ∀ s ∈ Ioc 0 R₀, 0 ≤ h s)
    (hh : ∀ s ∈ Ioc 0 R₀, h s ≤ k / 2 * s)
    (ht : Tendsto (fun x => h x / x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun x => radiusMajorant h R₀ k x / x) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (ht.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 4)))
  filter_upwards [Ioo_mem_nhdsGT (lt_min hR (half_pos hδ))] with x hx
  have hx' : x ∈ Ioc 0 R₀ := ⟨hx.1, (lt_of_lt_of_le hx.2 (min_le_left _ _)).le⟩
  have hloc : ∀ s ∈ Ioc 0 R₀, s < 2 * x → h s ≤ (ε / 2) / 2 * s := by
    intro s hs hsx
    have hxδ : x < δ / 2 := lt_of_lt_of_le hx.2 (min_le_right _ _)
    have hb := hδb (show s ∈ Ioo 0 δ from ⟨hs.1, by linarith⟩)
    have he := (div_lt_iff₀ hs.1).mp hb
    linarith
  have hb := radiusMajorant_local_bound hk hx' (by positivity : 0 ≤ ε / 2) hh hloc
  have hn : 0 ≤ radiusMajorant h R₀ k x / x :=
    div_nonneg ((hp x hx').trans (le_radiusMajorant hk hx' hh)) hx.1.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  exact ((div_le_iff₀ hx.1).mpr hb).trans_lt (by linarith)

/-- [internal]
A finite nonnegative mass integral has vanishing small-radius tails.
This is valid for every outer radius, with no normalization of that radius
and no measurability assumption on the nonnegative integrand. -/
theorem mass_tail_tendsto {f : ℝ → ℝ≥0∞} {R₀ : ℝ} (hR : 0 < R₀)
    (hint : (∫⁻ s in Ioc 0 R₀, f s) < ⊤) :
    Tendsto (fun x => ∫⁻ s in Ioc 0 x, f s) (𝓝[>] 0) (𝓝 0) := by
  have hb (x : ℝ) : (volume.restrict (Ioc 0 R₀)) (Ioc 0 x) ≤ ENNReal.ofReal x := by
    calc
      _ ≤ volume (Ioc 0 x) := Measure.restrict_le_self _
      _ = ENNReal.ofReal x := by simp [Real.volume_Ioc]
  have hz : Tendsto (fun x : ℝ => ENNReal.ofReal x) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto (0 : ℝ)))
  have hμ : Tendsto (fun x : ℝ => (volume.restrict (Ioc 0 R₀)) (Ioc 0 x))
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz (fun _ => bot_le) hb
  have ht := tendsto_setLIntegral_zero hint.ne hμ
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT hR] with x hx
  rw [Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (Ioc_subset_Ioc_right hx.2.le)]

/-- [node c:exterior#dyadic-radius-choice]
Choose the radii of `charged_SF_new_version.tex:L1098–L1105` from the two terminal
mass outputs. The seed is strictly positive, as required by the binding
addendum to internal project record. The chosen first radius may lie below any prescribed
`R₀`; a separate top interval is needed when retaining that original `R₀`.
All witnesses depend on the mass function, the outer radius and the seed. -/
theorem dyadic_radius_choice {M : ℝ → ℝ} {R₀ σ₀ : ℝ}
    (hR : 0 < R₀) (hσ : 0 < σ₀)
    (hsmall : Tendsto (fun x => M x / x) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ s in Ioc 0 R₀, ENNReal.ofReal (M s / s ^ 2)) < ⊤) :
    ∃ R : ℕ → ℝ,
      (∀ j, 0 < R j ∧ R j ≤ R₀) ∧
      (∀ j, R (j + 1) ≤ R j / 2) ∧
      Tendsto R atTop (𝓝 0) ∧
      (∀ j, (∫⁻ s in Ioc 0 (R j), ENNReal.ofReal (M s / s ^ 2)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j))) ∧
      (∀ j, ∀ s ∈ Ioc 0 (R j), M s / s ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2) := by
  have ht := mass_tail_tendsto hR hint
  have hchoice (j : ℕ) : ∃ r ∈ Ioc 0 R₀,
      (∀ x ∈ Ioc 0 r, (∫⁻ s in Ioc 0 x, ENNReal.ofReal (M s / s ^ 2)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j))) ∧
      (∀ s ∈ Ioc 0 r, M s / s ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2) := by
    have hp : (0 : ℝ) < ((1 / 2 : ℝ) ^ j * σ₀) ^ 2 := by positivity
    have hq : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j)) := by positivity
    have he := (ht.eventually (Iio_mem_nhds hq)).and
      (hsmall.eventually (Iio_mem_nhds hp))
    obtain ⟨r, hr, hrb⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp he
    refine ⟨min r R₀, ⟨lt_min hr hR, min_le_right _ _⟩, ?_, ?_⟩
    · intro x hx
      exact (hrb ⟨hx.1, hx.2.trans (min_le_left _ _)⟩).1.le
    · intro s hs
      exact (hrb ⟨hs.1, hs.2.trans (min_le_left _ _)⟩).2.le
  choose t htmem htint htsmall using hchoice
  let R : ℕ → ℝ := Nat.rec (t 0) (fun j r => min (t (j + 1)) (r / 2))
  have hpos (j : ℕ) : 0 < R j := by
    induction j with
    | zero => exact (htmem 0).1
    | succ j ih => exact lt_min (htmem (j + 1)).1 (half_pos ih)
  have hle (j : ℕ) : R j ≤ t j := by
    cases j with
    | zero => exact le_rfl
    | succ j => exact min_le_left _ _
  have hstep (j : ℕ) : R (j + 1) ≤ R j / 2 := min_le_right _ _
  have hgeom (j : ℕ) : R j ≤ (1 / 2 : ℝ) ^ j * t 0 := by
    induction j with
    | zero => simp [R]
    | succ j ih =>
      calc
        R (j + 1) ≤ R j / 2 := hstep j
        _ ≤ ((1 / 2 : ℝ) ^ j * t 0) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (j + 1) * t 0 := by rw [pow_succ]; ring
  refine ⟨R, (fun j => ⟨hpos j, (hle j).trans (htmem j).2⟩), hstep, ?_, ?_, ?_⟩
  · apply squeeze_zero (fun j => (hpos j).le) hgeom
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (t 0)
  · intro j
    exact htint j (R j) ⟨hpos j, hle j⟩
  · intro j s hs
    exact htsmall j s ⟨hs.1, hs.2.trans (hle j)⟩

/-- [def-node c:exterior#step-radius-profile]
The piecewise linear radius of `charged_SF_new_version.tex:L1107`. On a dyadic annulus
the index set in this supremum is a singleton. Values are used only on
the union of those annuli. -/
@[expose] noncomputable def stepRadiusProfile (R : ℕ → ℝ) (σ₀ x : ℝ) : ℝ :=
  sSup ((fun j => (1 / 2 : ℝ) ^ j * σ₀ * x) ''
    {j | x ∈ Ioc (R (j + 1)) (R j)})

private theorem annular_index_unique {R : ℕ → ℝ} (hR : Antitone R)
    {x : ℝ} {i j : ℕ} (hi : x ∈ Ioc (R (i + 1)) (R i))
    (hj : x ∈ Ioc (R (j + 1)) (R j)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hji
  · exact False.elim (not_lt_of_ge (hj.2.trans (hR (Nat.succ_le_of_lt hij))) hi.1)
  · exact hij
  · exact False.elim (not_lt_of_ge (hi.2.trans (hR (Nat.succ_le_of_lt hji))) hj.1)

/-- [internal]
The step radius has exactly its displayed linear value on each annulus;
the half-open endpoint convention is retained. -/
theorem stepRadiusProfile_eq {R : ℕ → ℝ} (hR : Antitone R) {σ₀ x : ℝ} {j : ℕ}
    (hx : x ∈ Ioc (R (j + 1)) (R j)) :
    stepRadiusProfile R σ₀ x = (1 / 2 : ℝ) ^ j * σ₀ * x := by
  have hi : {i | x ∈ Ioc (R (i + 1)) (R i)} = {j} := by
    ext i
    exact ⟨fun h => annular_index_unique hR h hx, fun h => h ▸ hx⟩
  unfold stepRadiusProfile
  rw [hi]
  simp

/-- [internal]
Every positive radius up to the first selected radius belongs to an
annulus. This explicitly includes every dyadic jump endpoint. -/
theorem exists_dyadic_annulus {R : ℕ → ℝ} (hR : Antitone R)
    (ht : Tendsto R atTop (𝓝 0)) {x : ℝ} (hx : x ∈ Ioc 0 (R 0)) :
    ∃ j, x ∈ Ioc (R (j + 1)) (R j) := by
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hx.1)).exists
  have he : ∃ j, R (j + 1) < x :=
    ⟨n, (hR (Nat.le_succ n)).trans_lt hn⟩
  refine ⟨Nat.find he, Nat.find_spec he, ?_⟩
  cases hf : Nat.find he with
  | zero => simpa [hf] using hx.2
  | succ j =>
    have hm := Nat.find_min he (show j < Nat.find he by omega)
    simpa [hf] using le_of_not_gt hm

/-- [internal]
The step radius is positive and lies below `(σ₀)x`; its bound is uniform
over the selected annuli. -/
theorem stepRadiusProfile_bounds {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0))
    (hσ : 0 < σ₀) {x : ℝ} (hx : x ∈ Ioc 0 (R 0)) :
    0 < stepRadiusProfile R σ₀ x ∧ stepRadiusProfile R σ₀ x ≤ σ₀ * x := by
  obtain ⟨j, hj⟩ := exists_dyadic_annulus hR ht hx
  rw [stepRadiusProfile_eq hR hj]
  constructor
  · exact mul_pos (mul_pos (by positivity) hσ) hx.1
  · have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_right hp (mul_nonneg hσ.le hx.1.le)]

/-- [internal]
The dyadic step profile is nondecreasing, although it has upward jumps.
The seed and radius sequence are fixed before this assertion. -/
theorem stepRadiusProfile_monotoneOn {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : StrictAnti R) (ht : Tendsto R atTop (𝓝 0)) (hσ : 0 ≤ σ₀) :
    MonotoneOn (stepRadiusProfile R σ₀) (Ioc 0 (R 0)) := by
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := exists_dyadic_annulus hR.antitone ht hx
  obtain ⟨j, hj⟩ := exists_dyadic_annulus hR.antitone ht hy
  have hji : j ≤ i := by
    by_contra hn
    have hij : i + 1 ≤ j := by omega
    have hb := hR.antitone hij
    linarith [hi.1, hj.2]
  rw [stepRadiusProfile_eq hR.antitone hi, stepRadiusProfile_eq hR.antitone hj]
  have hp : (1 / 2 : ℝ) ^ i ≤ (1 / 2 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hji
  exact mul_le_mul (mul_le_mul_of_nonneg_right hp hσ) hxy hx.1.le (by positivity)

/-- [internal]
Below the `j`th selected radius, every active profile coefficient is at
most the `j`th dyadic coefficient. -/
theorem stepRadiusProfile_div_le {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0)) (hσ : 0 ≤ σ₀)
    {x : ℝ} {j : ℕ} (hx : x ∈ Ioc 0 (R j)) :
    stepRadiusProfile R σ₀ x / x ≤ (1 / 2 : ℝ) ^ j * σ₀ := by
  obtain ⟨i, hi⟩ := exists_dyadic_annulus hR ht
    (show x ∈ Ioc 0 (R 0) from ⟨hx.1, hx.2.trans (hR (Nat.zero_le j))⟩)
  have hji : j ≤ i := by
    by_contra hn
    have hle := hR (show i + 1 ≤ j by omega)
    linarith [hi.1, hx.2]
  rw [stepRadiusProfile_eq hR hi, mul_div_cancel_right₀ _ hx.1.ne']
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hji) hσ

/-- [internal]
The step profile is little-o of the radius, uniformly over all its
dyadic annuli. -/
theorem stepRadiusProfile_tendsto_div {R : ℕ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0))
    (hpos : ∀ j, 0 < R j) (hσ : 0 < σ₀) :
    Tendsto (fun x => stepRadiusProfile R σ₀ x / x) (𝓝[>] 0) (𝓝 0) := by
  have hσt : Tendsto (fun j => (1 / 2 : ℝ) ^ j * σ₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const σ₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (hσt.eventually (Iio_mem_nhds hε)).exists
  filter_upwards [Ioo_mem_nhdsGT (hpos j)] with x hx
  have hx' : x ∈ Ioc 0 (R 0) :=
    ⟨hx.1, hx.2.le.trans (hR (Nat.zero_le j))⟩
  have hn := (stepRadiusProfile_bounds hR ht hσ hx').1.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hn hx.1.le)]
  exact (stepRadiusProfile_div_le hR ht hσ.le ⟨hx.1, hx.2.le⟩).trans_lt hj

/-- [internal]
The pointwise dyadic mass bounds control mass divided by the step
radius on every annulus. -/
theorem mass_div_stepRadiusProfile_le {R : ℕ → ℝ} {M : ℝ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0)) (hσ : 0 < σ₀)
    (hm : ∀ j, ∀ x ∈ Ioc 0 (R j), M x / x ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2)
    {x : ℝ} {j : ℕ} (hx : x ∈ Ioc 0 (R j)) :
    M x / stepRadiusProfile R σ₀ x ≤ (1 / 2 : ℝ) ^ j * σ₀ := by
  obtain ⟨i, hi⟩ := exists_dyadic_annulus hR ht
    (show x ∈ Ioc 0 (R 0) from ⟨hx.1, hx.2.trans (hR (Nat.zero_le j))⟩)
  have hji : j ≤ i := by
    by_contra hn
    have hle := hR (show i + 1 ≤ j by omega)
    linarith [hi.1, hx.2]
  have hc : 0 < (1 / 2 : ℝ) ^ i * σ₀ := by positivity
  have hb := (div_le_iff₀ hx.1).mp (hm i x ⟨hx.1, hi.2⟩)
  rw [stepRadiusProfile_eq hR hi]
  calc
    M x / ((1 / 2 : ℝ) ^ i * σ₀ * x) ≤ (1 / 2 : ℝ) ^ i * σ₀ := by
      apply (div_le_iff₀ (mul_pos hc hx.1)).mpr
      nlinarith only [hb]
    _ ≤ (1 / 2 : ℝ) ^ j * σ₀ := mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hji) hσ.le

/-- [internal]
The mass-to-step-radius ratio vanishes at zero. Nonnegativity is used
only for the lower half of the squeeze. -/
theorem mass_div_stepRadiusProfile_tendsto {R : ℕ → ℝ} {M : ℝ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0))
    (hpos : ∀ j, 0 < R j) (hσ : 0 < σ₀)
    (hM : ∀ x ∈ Ioc 0 (R 0), 0 ≤ M x)
    (hm : ∀ j, ∀ x ∈ Ioc 0 (R j), M x / x ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2) :
    Tendsto (fun x => M x / stepRadiusProfile R σ₀ x) (𝓝[>] 0) (𝓝 0) := by
  have hσt : Tendsto (fun j => (1 / 2 : ℝ) ^ j * σ₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const σ₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (hσt.eventually (Iio_mem_nhds hε)).exists
  filter_upwards [Ioo_mem_nhdsGT (hpos j)] with x hx
  have hx' : x ∈ Ioc 0 (R 0) :=
    ⟨hx.1, hx.2.le.trans (hR (Nat.zero_le j))⟩
  have hn := (stepRadiusProfile_bounds hR ht hσ hx').1.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hM x hx') hn)]
  exact (mass_div_stepRadiusProfile_le hR ht hσ hm ⟨hx.1, hx.2.le⟩).trans_lt hj

/-- [internal]
The selected half-open annuli cover the positive interval up to the
first selected radius, including all dyadic endpoints. -/
theorem iUnion_dyadic_annuli {R : ℕ → ℝ} (hR : Antitone R)
    (ht : Tendsto R atTop (𝓝 0)) (hpos : ∀ j, 0 < R j) :
    (⋃ j, Ioc (R (j + 1)) (R j)) = Ioc 0 (R 0) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(hpos (j + 1)).trans hj.1, hj.2.trans (hR (Nat.zero_le j))⟩
  · exact exists_dyadic_annulus hR ht

/-- [internal]
The reciprocal-square mass weight is integrable on the selected dyadic
interval. Its bound depends on the positive seed, uniformly in the mass
function and the radius sequence satisfying the displayed dyadic bounds. -/
theorem adaptive_weight_integrable_of_dyadic {R : ℕ → ℝ} {M ell : ℝ → ℝ} {σ₀ : ℝ}
    (hR : Antitone R) (ht : Tendsto R atTop (𝓝 0)) (hpos : ∀ j, 0 < R j)
    (hσ : 0 < σ₀)
    (hM : ∀ x ∈ Ioc 0 (R 0), 0 ≤ M x)
    (hell : ∀ x ∈ Ioc 0 (R 0), stepRadiusProfile R σ₀ x ≤ ell x)
    (hI : ∀ j, (∫⁻ x in Ioc 0 (R j), ENNReal.ofReal (M x / x ^ 2)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j))) :
    (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) ≤
        ∑' j : ℕ, ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) ∧
      (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) < ⊤ := by
  have hbound (j : ℕ) : (∫⁻ x in Ioc (R (j + 1)) (R j),
      ENNReal.ofReal (M x / ell x ^ 2)) ≤
      ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) := by
    let c : ℝ := (1 / 2 : ℝ) ^ j * σ₀
    have hc : 0 < c := by dsimp [c]; positivity
    calc
      _ ≤ ∫⁻ x in Ioc (R (j + 1)) (R j),
          ENNReal.ofReal (c⁻¹ ^ 2) * ENNReal.ofReal (M x / x ^ 2) := by
        apply setLIntegral_mono' measurableSet_Ioc
        intro x hx
        have hx' : x ∈ Ioc 0 (R 0) :=
          ⟨(hpos (j + 1)).trans hx.1, hx.2.trans (hR (Nat.zero_le j))⟩
        have hh := hell x hx'
        rw [stepRadiusProfile_eq hR hx] at hh
        change c * x ≤ ell x at hh
        have hp := mul_pos hc hx'.1
        have hle : M x / ell x ^ 2 ≤ c⁻¹ ^ 2 * (M x / x ^ 2) := by
          calc
            _ ≤ M x / (c * x) ^ 2 := div_le_div_of_nonneg_left
              (hM x hx') (sq_pos_of_pos hp) (pow_le_pow_left₀ hp.le hh 2)
            _ = _ := by field_simp
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal (c⁻¹ ^ 2) *
          ∫⁻ x in Ioc (R (j + 1)) (R j), ENNReal.ofReal (M x / x ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (c⁻¹ ^ 2) *
          ∫⁻ x in Ioc 0 (R j), ENNReal.ofReal (M x / x ^ 2) := by
        gcongr
        exact (hpos (j + 1)).le
      _ ≤ ENNReal.ofReal (c⁻¹ ^ 2) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j)) :=
        mul_le_mul le_rfl (hI j) (by positivity) (by positivity)
      _ = ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        congr 1
        dsimp [c]
        have hp : (1 / 2 : ℝ) ^ j ≠ 0 := by positivity
        have hs : σ₀ ≠ 0 := hσ.ne'
        rw [show 4 * j = j * 4 by omega, pow_mul,
          show (1 / 4 : ℝ) ^ j = ((1 / 2 : ℝ) ^ j) ^ 2 by
            rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num]
        field_simp
  have hsummable : Summable (fun j : ℕ => σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _
  have hle : (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) ≤
      ∑' j : ℕ, ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) := by
    rw [← iUnion_dyadic_annuli hR ht hpos]
    exact (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hbound)
  exact ⟨hle, hle.trans_lt hsummable.tsum_ofReal_lt_top⟩

/-- [internal]
The majorant of the selected dyadic profile is positive, monotone and
`k`-Lipschitz, with both vanishing ratios and finite reciprocal-square
mass weight (`charged_SF_new_version.tex:L1072–L1138`, positive-seed addendum).
The slope is the prescribed `k`; the integral bound depends on `σ₀`.
This theorem concerns the interval up to the first selected radius. -/
theorem adaptive_radius_properties {R : ℕ → ℝ} {M : ℝ → ℝ} {σ₀ k : ℝ}
    (hk : 0 < k ∧ k < 1 / 8) (hσ : 0 < σ₀ ∧ σ₀ < k / 2)
    (hpos : ∀ j, 0 < R j) (hhalve : ∀ j, R (j + 1) ≤ R j / 2)
    (ht : Tendsto R atTop (𝓝 0)) (hM : ∀ x ∈ Ioc 0 (R 0), 0 ≤ M x)
    (hm : ∀ j, ∀ x ∈ Ioc 0 (R j), M x / x ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2)
    (hI : ∀ j, (∫⁻ x in Ioc 0 (R j), ENNReal.ofReal (M x / x ^ 2)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j))) :
    let ell := radiusMajorant (stepRadiusProfile R σ₀) (R 0) k
    MonotoneOn ell (Ioc 0 (R 0)) ∧
      LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (R 0)) ∧
      (∀ x ∈ Ioc 0 (R 0), 0 < ell x ∧ ell x ≤ k * x) ∧
      Tendsto (fun x => ell x / x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => M x / ell x) (𝓝[>] 0) (𝓝 0) ∧
      (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) ≤
        ∑' j : ℕ, ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) ∧
      (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) < ⊤ := by
  have hR : StrictAnti R := strictAnti_nat_of_succ_lt (fun j =>
    (hhalve j).trans_lt (by have hp := hpos j; linarith))
  let ell := radiusMajorant (stepRadiusProfile R σ₀) (R 0) k
  have hb (x : ℝ) (hx : x ∈ Ioc 0 (R 0)) :
      stepRadiusProfile R σ₀ x ≤ k / 2 * x :=
    ((stepRadiusProfile_bounds hR.antitone ht hσ.1 hx).2).trans
      (mul_le_mul_of_nonneg_right hσ.2.le hx.1.le)
  have hdom (x : ℝ) (hx : x ∈ Ioc 0 (R 0)) : stepRadiusProfile R σ₀ x ≤ ell x :=
    le_radiusMajorant hk.1.le hx hb
  have hpositive (x : ℝ) (hx : x ∈ Ioc 0 (R 0)) : 0 < ell x :=
    ((stepRadiusProfile_bounds hR.antitone ht hσ.1 hx).1).trans_le (hdom x hx)
  refine ⟨radiusMajorant_monotoneOn hk.1.le (stepRadiusProfile_monotoneOn hR ht hσ.1.le) hb,
    radiusMajorant_lipschitzOnWith hk.1.le (stepRadiusProfile_monotoneOn hR ht hσ.1.le) hb,
    ?_, ?_, ?_, adaptive_weight_integrable_of_dyadic hR.antitone ht hpos hσ.1 hM hdom hI⟩
  · intro x hx
    refine ⟨hpositive x hx, (radiusMajorant_le hk.1.le hx hb).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith [hk.1] : k / 2 ≤ k) hx.1.le
  · exact radiusMajorant_tendsto_div (hpos 0) hk.1.le
      (fun x hx => (stepRadiusProfile_bounds hR.antitone ht hσ.1 hx).1.le) hb
      (stepRadiusProfile_tendsto_div hR.antitone ht hpos hσ.1)
  · apply squeeze_zero' _ _ (mass_div_stepRadiusProfile_tendsto hR.antitone ht hpos hσ.1 hM hm)
    · filter_upwards [Ioo_mem_nhdsGT (hpos 0)] with x hx
      exact div_nonneg (hM x ⟨hx.1, hx.2.le⟩) (hpositive x ⟨hx.1, hx.2.le⟩).le
    · filter_upwards [Ioo_mem_nhdsGT (hpos 0)] with x hx
      have hx' : x ∈ Ioc 0 (R 0) := ⟨hx.1, hx.2.le⟩
      exact div_le_div_of_nonneg_left (hM x hx')
        (stepRadiusProfile_bounds hR.antitone ht hσ.1 hx').1 (hdom x hx')

/-- [node c:exterior#adaptive-radius-properties]
All adaptive majorant properties, including domination of the step profile
(charged_SF_new_version.tex:L1072–1138). The slope is the prescribed `k`; the summable
integral bound depends on the positive seed `σ₀`, uniformly in the radius. -/
theorem adaptive_radius_properties_with_domination {R : ℕ → ℝ} {M : ℝ → ℝ} {σ₀ k : ℝ}
    (hk : 0 < k ∧ k < 1 / 8) (hσ : 0 < σ₀ ∧ σ₀ < k / 2)
    (hpos : ∀ j, 0 < R j) (hhalve : ∀ j, R (j + 1) ≤ R j / 2)
    (ht : Tendsto R atTop (𝓝 0)) (hM : ∀ x ∈ Ioc 0 (R 0), 0 ≤ M x)
    (hm : ∀ j, ∀ x ∈ Ioc 0 (R j), M x / x ≤ ((1 / 2 : ℝ) ^ j * σ₀) ^ 2)
    (hI : ∀ j, (∫⁻ x in Ioc 0 (R j), ENNReal.ofReal (M x / x ^ 2)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (4 * j))) :
    let ell := radiusMajorant (stepRadiusProfile R σ₀) (R 0) k
    MonotoneOn ell (Ioc 0 (R 0)) ∧
      LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 (R 0)) ∧
      (∀ x ∈ Ioc 0 (R 0), 0 < ell x ∧ ell x ≤ k * x) ∧
      Tendsto (fun x => ell x / x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => M x / ell x) (𝓝[>] 0) (𝓝 0) ∧
      (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) ≤
        ∑' j : ℕ, ENNReal.ofReal (σ₀⁻¹ ^ 2 * (1 / 4 : ℝ) ^ j) ∧
      (∫⁻ x in Ioc 0 (R 0), ENNReal.ofReal (M x / ell x ^ 2)) < ⊤ ∧
      ∀ x ∈ Ioc 0 (R 0), stepRadiusProfile R σ₀ x ≤ ell x := by
  obtain ⟨hmono, hLip, hp, ht', hm', hbound, hfinite⟩ :=
    adaptive_radius_properties hk hσ hpos hhalve ht hM hm hI
  refine ⟨hmono, hLip, hp, ht', hm', hbound, hfinite, ?_⟩
  intro x hx
  have hanti : Antitone R := (strictAnti_nat_of_succ_lt (fun j =>
    (hhalve j).trans_lt (by have hj := hpos j; linarith))).antitone
  exact le_radiusMajorant hk.1.le hx (fun y hy =>
    (stepRadiusProfile_bounds hanti ht hσ.1 hy).2.trans
      (mul_le_mul_of_nonneg_right hσ.2.le hy.1.le))

end EmcsfAcExtension.Global.Exterior
