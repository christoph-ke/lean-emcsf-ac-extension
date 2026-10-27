module

public import EmcsfAcExtension.Global.Observation.MaxwellPrimitive
public import EmcsfAcExtension.Frozen.Fields.PotentialV
public import EmcsfAcExtension.Infra.AC.Complex

/-! # The outward-anchored electric potential

The outer cylinder has zero potential in the boundary parallel gauge. Radius
is the outgoing variable in this file. Source: `charged_SF_new_version.tex:L2390–L2404`;
approved internal project record formula (A). The canonical outgoing radial mass data
used by the later comparison estimates follow from the component mass equation
(`charged_SF_new_version.tex:L2497–L2510`).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
The inverse-square radial kernel has its exact finite-endpoint primitive.
Neither endpoint is taken to zero. -/
theorem integral_inv_sq_outer {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, 1 / s ^ 2) = 1 / r - 1 / L := by
  have hs (s : ℝ) (hs : s ∈ uIcc r L) : s ≠ 0 := by
    have hx : s ∈ Icc r L := by simpa only [uIcc_of_le hrL] using hs
    exact ne_of_gt (hr.trans_le hx.1)
  have hc : ContinuousOn (fun s : ℝ => 1 / s ^ 2) (Icc r L) :=
    continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs' => pow_ne_zero 2 (ne_of_gt (hr.trans_le hs'.1)))
  have hd (s : ℝ) (hs' : s ∈ uIcc r L) :
      HasDerivAt (fun t : ℝ => -(t⁻¹)) (1 / s ^ 2) s := by
    simpa only [Pi.inv_apply, Pi.neg_apply, id_eq, neg_div, neg_neg, one_div] using!
      ((hasDerivAt_id s).inv (hs s hs')).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hrL : IntervalIntegrable (fun s : ℝ => 1 / s ^ 2) volume r L)
  simpa only [one_div, neg_sub_neg] using h

/-- [internal]
The normalized potential constraint has an inverse-square majorant with
universal coefficient `4`, once the improved charge bound is available. -/
theorem potential_radial_source_bound {s nu Q g : ℝ}
    (hs : 0 < s) (hnu : |nu| ≤ 1 / 2) (hQ : |Q| ≤ 2) (hg : 1 / 2 ≤ g) :
    |2 * nu * Q / (g * s ^ 2)| ≤ 4 / s ^ 2 := by
  have hg' : 0 < g := by linarith only [hg]
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (mul_pos hg' hs2)]
  have hn : 2 * |nu| * |Q| ≤ 2 := by
    calc
      2 * |nu| * |Q| ≤ 2 * (1 / 2) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hnu (by norm_num)) hQ
          (abs_nonneg Q) (by norm_num)
      _ = 2 := by norm_num
  apply (div_le_div_iff₀ (mul_pos hg' hs2) hs2).mpr
  have hleft := mul_le_mul_of_nonneg_right hn hs2.le
  have hright := mul_le_mul_of_nonneg_right hg hs2.le
  nlinarith only [hleft, hright]

/-- [internal]
The potential and its physical charged scale have a universal bound, chosen
before all solution data. Normalization supplies the radial potential
constraint, the zero outer-cylinder value, continuous coefficients, and the
outer optical and gap bounds. The charge bound is the prior Maxwell
improvement. There is no assumption that the normalized chart is an
`IsSolution` domain. -/
theorem co_potential_of_normalization :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e eta r L : ℝ) (H : ℂ) (A nu Q g : ℝ → ℝ),
        0 < r → r ≤ L →
        |e| * L * (1 + ‖H‖) = eta →
        ContinuousOn A (Icc r L) → ContinuousOn nu (Icc r L) →
        ContinuousOn Q (Icc r L) → ContinuousOn g (Icc r L) →
        (∀ s ∈ Ioo r L,
          HasDerivAt A (2 * nu s * Q s / (g s * s ^ 2)) s) →
        A L = 0 →
        (∀ s ∈ Icc r L, |nu s| ≤ 1 / 2 ∧ |Q s| ≤ 2 ∧ 1 / 2 ≤ g s) →
        |A r| ≤ C / r ∧ |e * A r| * (1 + ‖H‖) ≤ C * eta / (L * r) := by
  refine ⟨4, by norm_num, ?_⟩
  intro e eta r L H A nu Q g hr hrL heta hA hnu hQ hg hd hAL hbox
  have hL : 0 < L := hr.trans_le hrL
  have hpos (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hgc (s : ℝ) (hs : s ∈ Icc r L) : g s ≠ 0 := by
    have hh := (hbox s hs).2.2
    linarith only [hh]
  have hf : ContinuousOn (fun s => 2 * nu s * Q s / (g s * s ^ 2)) (Icc r L) :=
    ((continuousOn_const.mul hnu).mul hQ).div (hg.mul (continuousOn_id.pow 2))
      (fun s hs => mul_ne_zero (hgc s hs) (pow_ne_zero 2 (hpos s hs).ne'))
  have hi : IntervalIntegrable (fun s => 2 * nu s * Q s / (g s * s ^ 2)) volume r L :=
    hf.intervalIntegrable_of_Icc hrL
  have hkernel : IntervalIntegrable (fun s : ℝ => 4 / s ^ 2) volume r L :=
    (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hpos s hs).ne')).intervalIntegrable_of_Icc hrL
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrL hA hd hi
  have habound : |A r| ≤ 4 / r := by
    calc
      |A r| = |∫ s in r..L, 2 * nu s * Q s / (g s * s ^ 2)| := by
        rw [hFTC, hAL, zero_sub, abs_neg]
      _ ≤ ∫ s in r..L, |2 * nu s * Q s / (g s * s ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hrL
      _ ≤ ∫ s in r..L, 4 / s ^ 2 :=
        intervalIntegral.integral_mono_on hrL hi.abs hkernel (fun s hs =>
          potential_radial_source_bound (hpos s hs) (hbox s hs).1
            (hbox s hs).2.1 (hbox s hs).2.2)
      _ = 4 * (1 / r - 1 / L) := by
        simp_rw [show ∀ s : ℝ, 4 / s ^ 2 = 4 * (1 / s ^ 2) by intro s; ring]
        rw [intervalIntegral.integral_const_mul, integral_inv_sq_outer hr hrL]
      _ = 4 / r - 4 / L := by ring
      _ ≤ 4 / r := sub_le_self _ (div_nonneg (by norm_num) hL.le)
  refine ⟨habound, ?_⟩
  have he : 0 ≤ |e| * (1 + ‖H‖) := mul_nonneg (abs_nonneg _) (by positivity)
  calc
    |e * A r| * (1 + ‖H‖) = |e| * (1 + ‖H‖) * |A r| := by rw [abs_mul]; ring
    _ ≤ |e| * (1 + ‖H‖) * (4 / r) := mul_le_mul_of_nonneg_left habound he
    _ = 4 * eta / (L * r) := by
      rw [← heta]
      field_simp [hL.ne', hr.ne']

/-- [internal]
The potential estimate on an actual outgoing normalized characteristic.
Its radial coordinate and all radial hypotheses are constructed from the
component equations here. The universal constant is selected before every
field and physical datum. The improved charge bound is the prior Maxwell
conclusion on the same characteristic. -/
theorem co_potential_on_outgoing_of_normalization :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Fields) (e eta L u v : ℝ) (H : ℂ),
        v ≤ u → 0 < S.r u v → S.r u u = L →
        |e| * L * (1 + ‖H‖) = eta →
        ContinuousOn (S.r u) (Icc v u) → ContinuousOn (S.lam u) (Icc v u) →
        ContinuousOn (S.A u) (Icc v u) → ContinuousOn (S.nu u) (Icc v u) →
        ContinuousOn (S.Q u) (Icc v u) → ContinuousOn (S.m u) (Icc v u) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.r u) (S.lam u t) t) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.A u) (S.AV u t) t) →
        S.A u u = 0 →
        (∀ t ∈ Icc v u, 0 < S.lam u t ∧ |S.nu u t| ≤ 1 / 2 ∧
          |S.Q u t| ≤ 2 ∧ 1 / 2 ≤ 1 - S.mu u t) →
        |S.A u v| ≤ C / S.r u v ∧
          |e * S.A u v| * (1 + ‖H‖) ≤ C * eta / (L * S.r u v) := by
  obtain ⟨C, hC, hbound⟩ := co_potential_of_normalization
  refine ⟨C, hC, ?_⟩
  intro S e eta L u v H hvu hr hRL heta hcR _hcl hcA hcn hcQ hcm hdR hdA hAb hbox
  obtain ⟨inv, hmono, hci, hmem, hi, hleft, hright, hdi⟩ :=
    radial_section_inverse_of_normalization hvu hcR hdR
      (fun t ht => (hbox t (Ioo_subset_Icc_self ht)).1)
  simp only [hRL] at hi hright hdi
  have hrL : S.r u v ≤ L := by
    rw [← hRL]
    exact hmono.monotoneOn ⟨le_rfl, hvu⟩ ⟨hvu, le_rfl⟩ hvu
  let A : ℝ → ℝ := fun s => S.A u (inv s)
  let nu : ℝ → ℝ := fun s => S.nu u (inv s)
  let Q : ℝ → ℝ := fun s => S.Q u (inv s)
  let g : ℝ → ℝ := fun s => 1 - 2 * S.m u (inv s) / s
  have hAc : ContinuousOn A (Icc (S.r u v) L) :=
    hcA.comp hci.continuousOn (fun t _ => hmem t)
  have hnc : ContinuousOn nu (Icc (S.r u v) L) :=
    hcn.comp hci.continuousOn (fun t _ => hmem t)
  have hQc : ContinuousOn Q (Icc (S.r u v) L) :=
    hcQ.comp hci.continuousOn (fun t _ => hmem t)
  have hgc : ContinuousOn g (Icc (S.r u v) L) :=
    continuousOn_const.sub ((continuousOn_const.mul
      (hcm.comp hci.continuousOn (fun t _ => hmem t))).div continuousOn_id
        (fun s hs => (hr.trans_le hs.1).ne'))
  have hAd (s : ℝ) (hs : s ∈ Ioo (S.r u v) L) :
      HasDerivAt A (2 * nu s * Q s / (g s * s ^ 2)) s := by
    have hl := (hbox (inv s) (hmem s)).1.ne'
    convert (hdA (inv s) (hdi s hs).1).scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [Fields.AV, Fields.mu, nu, Q, g]
      rw [hi s ⟨hs.1.le, hs.2.le⟩]
      simp only [smul_eq_mul]
      field_simp
  have hresult := hbound e eta (S.r u v) L H A nu Q g hr hrL heta
    hAc hnc hQc hgc hAd (by simpa only [A, hright] using hAb)
    (fun s hs => ⟨(hbox (inv s) (hmem s)).2.1,
      (hbox (inv s) (hmem s)).2.2.1, by
        have h := (hbox (inv s) (hmem s)).2.2.2
        simpa only [Fields.mu, hi s hs, g] using h⟩)
  simpa only [A, hleft] using hresult

/-- [internal]
The canonical inverse of radius on an actual outgoing normalized section
supplies continuous scalar, mass and charge profiles, the radial mass equation,
absolute continuity of mass and scalar energy at most `8`. These data follow
from the component equations, positive outgoing expansion, mass in `[0,2]`
and the gap `1/2`; no comparison estimate or normalized `IsSolution` is assumed.
The section may degenerate. All coefficients are exact and universal. -/
theorem outgoing_radial_mass_data_of_normalization
    (S : Fields) {u v L : ℝ} (hvu : v ≤ u) (hr : 0 < S.r u v) (hRL : S.r u u = L)
    (hcR : ContinuousOn (S.r u) (Icc v u)) (hcl : ContinuousOn (S.lam u) (Icc v u))
    (hct : ContinuousOn (S.theta u) (Icc v u)) (hcm : ContinuousOn (S.m u) (Icc v u))
    (hcQ : ContinuousOn (S.Q u) (Icc v u))
    (hdR : ∀ t ∈ Ioo v u, HasDerivAt (S.r u) (S.lam u t) t)
    (hdm : ∀ t ∈ Ioo v u, HasDerivAt (S.m u) (S.mV u t) t)
    (hbox : ∀ t ∈ Icc v u, 0 < S.lam u t ∧ S.m u t ∈ Icc 0 2 ∧
      1 / 2 ≤ 1 - S.mu u t) :
    ∃ inv : ℝ → ℝ,
      let y := fun s => S.theta u (inv s) / (S.lam u (inv s) : ℂ)
      let m := fun s => S.m u (inv s)
      let Q := fun s => S.Q u (inv s)
      S.r u v ≤ L ∧ Continuous inv ∧ (∀ s, inv s ∈ Icc v u) ∧
      (∀ s ∈ Icc (S.r u v) L, S.r u (inv s) = s) ∧
      inv (S.r u v) = v ∧ inv L = u ∧
      (∀ s ∈ Ioo (S.r u v) L, inv s ∈ Ioo v u ∧
        HasDerivAt inv (S.lam u (inv s))⁻¹ s) ∧
      ContinuousOn y (Icc (S.r u v) L) ∧ ContinuousOn m (Icc (S.r u v) L) ∧
      ContinuousOn Q (Icc (S.r u v) L) ∧
      (∀ s ∈ Ioo (S.r u v) L, HasDerivAt m
        ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s) ∧
      AbsolutelyContinuousOnInterval m (S.r u v) L ∧
      (∀ s ∈ Icc (S.r u v) L, m s ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - 2 * m s / s) ∧
      (∫ s in (S.r u v)..L, ‖y s‖ ^ 2) ≤ 8 := by
  obtain ⟨inv, hmono, hci, hmem, hi, hleft, hright, hdi⟩ :=
    radial_section_inverse_of_normalization hvu hcR hdR
      (fun t ht => (hbox t (Ioo_subset_Icc_self ht)).1)
  simp only [hRL] at hi hright hdi
  have hrL : S.r u v ≤ L := by
    rw [← hRL]
    exact hmono.monotoneOn ⟨le_rfl, hvu⟩ ⟨hvu, le_rfl⟩ hvu
  let y : ℝ → ℂ := fun s => S.theta u (inv s) / (S.lam u (inv s) : ℂ)
  let m : ℝ → ℝ := fun s => S.m u (inv s)
  let Q : ℝ → ℝ := fun s => S.Q u (inv s)
  have hmc : ContinuousOn m (Icc (S.r u v) L) :=
    hcm.comp hci.continuousOn (fun t _ => hmem t)
  have hQc : ContinuousOn Q (Icc (S.r u v) L) :=
    hcQ.comp hci.continuousOn (fun t _ => hmem t)
  have hyc : ContinuousOn y (Icc (S.r u v) L) :=
    (hct.comp hci.continuousOn (fun t _ => hmem t)).div
      (Complex.continuous_ofReal.comp_continuousOn
        (hcl.comp hci.continuousOn (fun t _ => hmem t)))
      (fun t _ => Complex.ofReal_ne_zero.mpr (hbox (inv t) (hmem t)).1.ne')
  have hmd (s : ℝ) (hs : s ∈ Ioo (S.r u v) L) :
      HasDerivAt m ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s := by
    have hl := (hbox (inv s) (hmem s)).1.ne'
    convert (hdm (inv s) (hdi s hs).1).scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [Fields.mV, Fields.mu, m, Q, y]
      rw [hi s ⟨hs.1.le, hs.2.le⟩]
      simp only [smul_eq_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        div_pow, sq_abs]
      field_simp
  have hradbox (s : ℝ) (hs : s ∈ Icc (S.r u v) L) :
      m s ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - 2 * m s / s := by
    refine ⟨(hbox (inv s) (hmem s)).2.1, ?_⟩
    have h := (hbox (inv s) (hmem s)).2.2
    simpa only [Fields.mu, hi s hs, m] using h
  let F := fun s => (1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)
  have hFc : ContinuousOn F (Icc (S.r u v) L) := by
    have hgap : ContinuousOn (fun s => 1 - 2 * m s / s) (Icc (S.r u v) L) :=
      continuousOn_const.sub ((continuousOn_const.mul hmc).div continuousOn_id
        (fun s hs => (hr.trans_le hs.1).ne'))
    exact ((hgap.mul (hyc.norm.pow 2)).div_const 2).add
      ((hQc.pow 2).div (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr.trans_le hs.1).ne')))
  have hFi : IntervalIntegrable F volume (S.r u v) L := hFc.intervalIntegrable_of_Icc hrL
  have hmac : AbsolutelyContinuousOnInterval m (S.r u v) L := by
    apply (AbsolutelyContinuousOnInterval.iff_exists_integral_real hrL).mpr
    refine ⟨F, hFi, ?_⟩
    intro s hs
    have hsub : Icc (S.r u v) s ⊆ Icc (S.r u v) L := Icc_subset_Icc le_rfl hs.2
    have hiSub : IntervalIntegrable F volume (S.r u v) s :=
      hFi.mono_set (by simpa only [uIcc_of_le hs.1, uIcc_of_le hrL] using hsub)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1
      (hmc.mono hsub) (fun t ht => hmd t ⟨ht.1, ht.2.trans_le hs.2⟩) hiSub
    linarith only [hFTC]
  exact ⟨inv, hrL, hci, hmem, hi, hleft, hright, hdi, hyc, hmc, hQc, hmd, hmac, hradbox,
    radial_scalar_energy_of_normalization hr hrL hmc hQc hyc hmd hradbox⟩
/-- [internal]
Joint continuity restricts to every actual outward characteristic in the
same dependence triangle. This assertion uses the literal truncated set. -/
theorem continuousOn_outgoing_of_subtriangle {E : Type*} [TopologicalSpace E]
    {K : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {u v : ℝ}
    (hf : ContinuousOn (Function.uncurry f) K) (hsub : sidewaysTriangle v u ⊆ K) :
    ContinuousOn (f u) (Icc v u) := by
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq] using
    hf.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => hsub (sidewaysTriangle_outgoing ht))

/-- [internal]
The conditional Maxwell and potential bounds hold on the same literal
truncation as the scalar stop. Constants are chosen after the universal
static scalar bound `Kstatic` and boundary charge coefficient `Bboundary`,
before all normalized fields and physical data. The scalar stop is used
only to bound the shifted scalar; no improved charge is assumed.
Every outgoing component equation is a raw normalization input. -/
theorem Observation.outer_charge_potential_of_normalization
    (Kstatic : ℝ) (hK : 0 ≤ Kstatic) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ Bboundary : ℝ, 0 ≤ Bboundary →
    ∃ Cq : ℝ, 0 < Cq ∧
      ∀ (S : Fields) (D : Set (ℝ × ℝ)) (e eta a b rho L qStar : ℝ)
        (H : ℂ) (phiStar : ℝ → ℂ),
      let K := sidewaysTruncation S D a b rho L
      0 < rho → 1 ≤ L → |qStar| ≤ 1 →
      |e| * L * (1 + ‖H‖) = eta → Cq * eta ≤ 1 →
      comparisonNorm K (scalarComparison S H phiStar) ≤ 1 →
      (∀ p ∈ K, ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ ≤ Kstatic) →
      (∀ p ∈ K, sidewaysTriangle p.2 p.1 ⊆ K) →
      ContinuousOn (Function.uncurry S.r) K → ContinuousOn (Function.uncurry S.lam) K →
      ContinuousOn (Function.uncurry S.nu) K → ContinuousOn (Function.uncurry S.m) K →
      ContinuousOn (Function.uncurry S.Q) K → ContinuousOn (Function.uncurry S.A) K →
      ContinuousOn (Function.uncurry S.phi) K → ContinuousOn (Function.uncurry S.theta) K →
      (∀ p ∈ K, 0 < S.lam p.1 p.2 ∧ |S.nu p.1 p.2| ≤ 1 / 2 ∧
        S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2) →
      (∀ p ∈ K, ∀ t ∈ Ioo p.2 p.1,
        HasDerivAt (S.r p.1) (S.lam p.1 t) t ∧
        HasDerivAt (S.phi p.1) (S.phiV p.1 t) t ∧
        HasDerivAt (S.Q p.1) (S.QV e p.1 t) t ∧
        HasDerivAt (S.m p.1) (S.mV p.1 t) t ∧
        HasDerivAt (S.A p.1) (S.AV p.1 t) t) →
      (∀ t, (t, t) ∈ K → S.r t t = L ∧ S.A t t = 0 ∧
        |S.Q t t - qStar| ≤ Bboundary * eta) →
      ∀ p ∈ K,
        |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
        |S.A p.1 p.2| ≤ Cp / S.r p.1 p.2 ∧
        |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2) := by
  obtain ⟨Cp, hCp, hpotential⟩ := co_potential_on_outgoing_of_normalization
  refine ⟨Cp, hCp, fun Bboundary hB => ?_⟩
  obtain ⟨Cq, hCq, hcharge⟩ :=
    co_charge_improved_on_outgoing_of_normalization (Kstatic + 1) Bboundary (by positivity) hB
  refine ⟨Cq, hCq, ?_⟩
  intro S D e eta a b rho L qStar H phiStar
  dsimp only
  intro hrho hL hq heta hsmall hstop hstatic hsub hcR hcl hcn hcm hcQ hcA hcp hct hbox hd hb
  let K := sidewaysTruncation S D a b rho L
  have hsec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hf : ContinuousOn (Function.uncurry f) K) (p) (hp : p ∈ K) :=
    continuousOn_outgoing_of_subtriangle hf (hsub p hp)
  have hpsi (p) (hp : p ∈ K) : ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1 := by
    have he := (enorm_le_comparisonNorm hp).trans hstop
    have hw : ‖scalarComparison S H phiStar p.1 p.2‖ ≤ 1 := by
      simpa only [← ofReal_norm, ← ENNReal.ofReal_one,
        ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)] using he
    calc
      _ = ‖scalarComparison S H phiStar p.1 p.2 +
          (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by
        simp only [scalarComparison, sub_add_cancel]
      _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ +
          ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := norm_add_le _ _
      _ ≤ Kstatic + 1 := by linarith only [hw, hstatic p hp]
  have hQbound (p) (hp : p ∈ K) :
      |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 := by
    have hpath := (sidewaysTruncation_paths (hsub p hp)).2
    have huv := hp.1.2.2.1
    have hboundary := hb p.1 (hpath p.1 ⟨huv, le_rfl⟩)
    apply hcharge S e eta L p.1 p.2 qStar H huv (hrho.trans_le hp.2.1) hL hboundary.1 heta
      (hsec hcR p hp) (hsec hcl p hp) (hsec hcp p hp) (hsec hct p hp)
      (hsec hcQ p hp) (hsec hcm p hp)
      (fun t ht => (hd p hp t ht).1) (fun t ht => (hd p hp t ht).2.1)
      (fun t ht => (hd p hp t ht).2.2.1) (fun t ht => (hd p hp t ht).2.2.2.1)
      (fun t ht => ⟨(hbox (p.1, t) (hpath t ht)).1,
        (hbox (p.1, t) (hpath t ht)).2.2⟩)
      (fun t ht => hpsi (p.1, t) (hpath t ht)) hboundary.2.2 hq hsmall
  intro p hp
  have hpath := (sidewaysTruncation_paths (hsub p hp)).2
  have huv := hp.1.2.2.1
  have hboundary := hb p.1 (hpath p.1 ⟨huv, le_rfl⟩)
  have hA := hpotential S e eta L p.1 p.2 H huv (hrho.trans_le hp.2.1) hboundary.1 heta
    (hsec hcR p hp) (hsec hcl p hp) (hsec hcA p hp) (hsec hcn p hp)
    (hsec hcQ p hp) (hsec hcm p hp)
    (fun t ht => (hd p hp t ht).1) (fun t ht => (hd p hp t ht).2.2.2.2) hboundary.2.1
    (fun t ht => ⟨(hbox (p.1, t) (hpath t ht)).1,
      (hbox (p.1, t) (hpath t ht)).2.1,
      (hQbound (p.1, t) (hpath t ht)).2, (hbox (p.1, t) (hpath t ht)).2.2.2⟩)
  exact ⟨(hQbound p hp).1, (hQbound p hp).2, hA⟩

end EmcsfAcExtension.Global
