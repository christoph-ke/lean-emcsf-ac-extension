module

public import EmcsfAcExtension.Local.Broad.MassComparison
public import EmcsfAcExtension.Local.Broad.Charge
import EmcsfAcExtension.Local.Broad.PotentialAlgebra

/-! # Broad potential difference and scalar gauge cost

The zero-axis gauge is a separate premise. The density comparison keeps
both actual squared radii and the difference of the positive mass gaps.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

private theorem potential_deriv_out {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v)
    (hs : outSeg u u v ⊆ D) :
    ∀ x ∈ Ioo u v, HasDerivAt (S.A u) (S.AV u x) x := by
  have cr := continuousOn_out_section hS.cont_r hs
  have cn := continuousOn_out_section hS.cont_nu hs
  have cl := continuousOn_out_section hS.cont_lam hs
  have cQ := continuousOn_out_section hS.cont_Q hs
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Icc u v) :=
    continuousOn_const.sub (continuousOn_mu_out hS huv hs)
  have cd : ContinuousOn (S.AV u) (Ioo u v) := by
    apply ((((continuousOn_const.mul (cn.mono Ioo_subset_Icc_self)).mul
      (cl.mono Ioo_subset_Icc_self)).mul (cQ.mono Ioo_subset_Icc_self)).div
        ((cg.mono Ioo_subset_Icc_self).mul ((cr.mono Ioo_subset_Icc_self).pow 2)))
    intro x hx
    exact mul_ne_zero (hS.one_sub_mu_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2.le⟩)).ne'
      (pow_ne_zero 2 (hS.r_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2.le⟩) hx.1).ne')
  intro x hx
  apply hasDerivAt_of_integralForm_interior hx cd
  intro a b ha hab hb
  exact (hS.eq_out u a b ha hab (by
    rintro p ⟨rfl, hp⟩
    exact hs ⟨rfl, ha.le.trans hp.1, hp.2.trans hb.le⟩)).2.2.2.2.1

/-- [node restart-stab-broad-uniqueness#potential-and-scalar-gauge-cost]
Potential and incoming scalar gauge comparison, charged_SF_new_version.tex:L5787–5787
and internal project record (AP), (AG). For each fixed box `c,C`, the positive constant is
uniform in the coupling, scalar size, triangle, competing frozen solutions
and section label. Integrability of the scalar gauge cost is included.
The two zero-axis gauges are explicit; common initial data are unnecessary. -/
theorem potential_and_scalar_gauge_cost (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      let σ := e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2
      (∀ u v, (u, v) ∈ triangle s t →
        |S₁.A u v - S₂.A u v| ≤ K * |e| * M * ((t - s) / 2) * E) ∧
      ∀ v ∈ Icc s t,
        IntervalIntegrable (fun u => |e| *
          ‖(S₁.A u v : ℂ) * S₁.a u v - (S₂.A u v : ℂ) * S₂.a u v‖) volume s v ∧
        (∫ u in s..v, |e| *
          ‖(S₁.A u v : ℂ) * S₁.a u v - (S₂.A u v : ℂ) * S₂.a u v‖) ≤ K * σ * E := by
  obtain ⟨Kq, hKq, hcharge⟩ := charge_comparison c C hc hC
  obtain ⟨Kμ, hKμ, hmass⟩ := Local.stab_broad_mu_sup c C hc hC
  let k := C / c
  let B := 2 * ((C ^ 2 / c) * (Kq + (1 + k)) + 2 * C / c +
    (C ^ 2 / c ^ 2) * (2 * Kμ))
  let CA := C ^ 2 / c ^ 2
  let J := 2 * B + CA * C
  let K := 2 * B + 4 * J + 1
  have hk : 0 ≤ k := div_nonneg hC hc.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hng haxis hosc hσ E σ
  have hm₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hm₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  let G := (geometry_distance s t S₁ S₂).toReal
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hεG : ε * G ≤ E := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hD : (normalized_field_distance s t S₁ S₂).toReal ≤ E :=
    le_add_of_nonneg_right (mul_nonneg hε hG)
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hbox S₁ hm₁ p hp).1)
  have hmass' := hmass s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hbox hosc
  have hX : (mass_ratio_distance s t S₁ S₂).toReal ≤ 2 * Kμ * ε * E := by
    calc
      _ ≤ Kμ * ε * (normalized_field_distance s t S₁ S₂).toReal +
          Kμ * ε ^ 2 * G + Kμ * σ * ε * E := hmass'
      _ = Kμ * ε * E + Kμ * σ * ε * E := by dsimp [E, G]; ring
      _ ≤ Kμ * ε * E + Kμ * 1 * ε * E := by gcongr
      _ = _ := by ring
  have hQ := hcharge s t e M ε S₁ S₂ hS₁ hS₂ hM hε hε1 hbox hosc
  have hδdensity u v (hp : (u, v) ∈ triangle s t) (huv : u < v) :
      |S₁.AV u v - S₂.AV u v| ≤ B * |e| * M * E := by
    have hr₁ := hS₁.r_pos (u, v) hp huv
    have hr₂ := hS₂.r_pos (u, v) hp huv
    have hs : outSeg u u v ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
    have hRratio : S₂.r u v ≤ k * S₁.r u v := by
      have hlo := outgoing_radius_lower hS₁ huv.le hs
        (fun x hx => (hbox S₁ hm₁ (u, x) (hs ⟨rfl, hx⟩)).1)
      calc
        _ ≤ C * (v - u) := outgoing_radius_upper hS₂ huv.le hs
          (fun x hx => (hbox S₂ hm₂ (u, x) (hs ⟨rfl, hx⟩)).2.1)
        _ = k * (c * (v - u)) := by dsimp [k]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlo hk
    have hq₂ : |S₂.Q u v| ≤ (|e| * M) * ε * S₂.r u v ^ 2 := by
      have h0 : 0 ≤ |e| * M * ε * S₂.r u v ^ 2 := by positivity
      exact (hQ u v hp).1.2.trans (by linarith)
    have hδq := charge_quotient_difference_of_bounds hr₁ hr₂
      (mul_nonneg (abs_nonneg e) hM0) hε hE hG hk hKq.le hRratio hq₂
      (by simpa only [mul_assoc] using (hQ u v hp).2)
      (abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp) hεG
    have hq₂' : |S₂.Q u v / S₂.r u v ^ 2| ≤ |e| * M * ε := by
      rw [abs_div, abs_of_pos (sq_pos_of_pos hr₂)]
      exact (div_le_iff₀ (sq_pos_of_pos hr₂)).mpr hq₂
    have hδgap : |(1 - S₁.mu u v) - (1 - S₂.mu u v)| ≤ 2 * Kμ * ε * E := by
      rw [show (1 - S₁.mu u v) - (1 - S₂.mu u v) = -(S₁.mu u v - S₂.mu u v) by ring,
        abs_neg]
      exact (abs_mu_sub_le_mass_ratio_distance hS₁ hS₂ hp).trans hX
    have hn {S : Fields} (hS : IsSolution e S (triangle s t)) (hm : S ∈ ({S₁, S₂} : Set Fields)) :
        |S.nu u v| ≤ C := by
      rw [abs_of_neg (hS.nu_neg (u, v) hp)]
      exact (hng S hm (u, v) hp).1
    have hl {S : Fields} (hS : IsSolution e S (triangle s t)) (hm : S ∈ ({S₁, S₂} : Set Fields)) :
        |S.lam u v| ≤ C := by
      rw [abs_of_pos (hS.lam_pos (u, v) hp)]
      exact (hbox S hm (u, v) hp).2.1
    have hfactor := potential_factor_difference_of_bounds hc hC hG (by positivity)
      (hn hS₁ hm₁) (hn hS₂ hm₂) (hl hS₁ hm₁) (hl hS₂ hm₂)
      (hng S₁ hm₁ (u, v) hp).2 (hng S₂ hm₂ (u, v) hp).2
      (abs_nu_sub_le_geometry_distance hS₁ hfin hp)
      (abs_lam_sub_le_geometry_distance hS₁ hfin hp) hδgap
    let P₁ := S₁.nu u v * S₁.lam u v / (1 - S₁.mu u v)
    let P₂ := S₂.nu u v * S₂.lam u v / (1 - S₂.mu u v)
    let q₁ := S₁.Q u v / S₁.r u v ^ 2
    let q₂ := S₂.Q u v / S₂.r u v ^ 2
    have heq (S : Fields) : S.AV u v =
        2 * ((S.nu u v * S.lam u v / (1 - S.mu u v)) * (S.Q u v / S.r u v ^ 2)) := by
      simp only [Fields.AV, div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq S₁, heq S₂, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hprod := (abs_product_sub_le P₁ q₁ P₂ q₂).trans
      (add_le_add (mul_le_mul hfactor.1 hδq (abs_nonneg _) (by positivity))
        (mul_le_mul hfactor.2 hq₂' (abs_nonneg _) (by positivity)))
    apply (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 2)).trans
    have hεsq : ε ^ 2 ≤ 1 := hsmall.trans (by norm_num)
    calc
      _ = (2 * (C ^ 2 / c) * (Kq + (1 + k))) * (|e| * M * E) +
          (4 * C / c) * (|e| * M * (ε * G)) +
          (2 * (C ^ 2 / c ^ 2) * (2 * Kμ)) * (|e| * M * (ε ^ 2 * E)) := by ring
      _ ≤ (2 * (C ^ 2 / c) * (Kq + (1 + k))) * (|e| * M * E) +
          (4 * C / c) * (|e| * M * E) +
          (2 * (C ^ 2 / c ^ 2) * (2 * Kμ)) * (|e| * M * (1 * E)) := by gcongr
      _ = _ := by dsimp [B]; ring
  have hA u v (hp : (u, v) ∈ triangle s t) :
      |S₁.A u v - S₂.A u v| ≤ B * |e| * M * (t - s) * E := by
    have hst : 0 ≤ t - s := by linarith [hp.1, hp.2.1, hp.2.2]
    rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
    · subst v
      rw [haxis S₁ hm₁ u ⟨hp.1, hp.2.2⟩, haxis S₂ hm₂ u ⟨hp.1, hp.2.2⟩,
        sub_self, abs_zero]
      positivity
    · have hs : outSeg u u v ⊆ triangle s t := by
        rintro p ⟨rfl, hx⟩
        exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
      have hd := abs_sub_le_of_interior_deriv_bound huv.le
        ((continuousOn_out_section hS₁.cont_A hs).sub (continuousOn_out_section hS₂.cont_A hs))
        (fun x hx => (potential_deriv_out hS₁ huv hs x hx).sub
          (potential_deriv_out hS₂ huv hs x hx))
        (fun x hx => hδdensity u x (hs ⟨rfl, hx.1.le, hx.2.le⟩) hx.1)
      change |(S₁.A u v - S₂.A u v) - (S₁.A u u - S₂.A u u)| ≤ _ at hd
      rw [haxis S₁ hm₁ u ⟨hp.1, huv.le.trans hp.2.2⟩,
        haxis S₂ hm₂ u ⟨hp.1, huv.le.trans hp.2.2⟩, sub_self, sub_zero] at hd
      apply hd.trans
      calc
        _ ≤ (B * |e| * M * E) * (t - s) :=
          mul_le_mul_of_nonneg_left (show v - u ≤ t - s by linarith [hp.1, hp.2.2])
            (by positivity)
        _ = _ := by ring
  refine ⟨?_, ?_⟩
  · intro u v hp
    have hst : 0 ≤ (t - s) / 2 := by linarith [hp.1, hp.2.1, hp.2.2]
    calc
      _ ≤ B * |e| * M * (t - s) * E := hA u v hp
      _ = (2 * B) * |e| * M * ((t - s) / 2) * E := by ring
      _ ≤ _ := by
        have hBK : 2 * B ≤ K := by dsimp [K]; linarith
        gcongr
  · intro v hv
    have hs : inSeg s v v ⊆ triangle s t := by
      rintro p ⟨hx, hy, rfl⟩
      exact ⟨hx, hy, hv.2⟩
    have ca₁ := continuousOn_in_section (IsSolution.cont_a hS₁) hs
    have ca₂ := continuousOn_in_section (IsSolution.cont_a hS₂) hs
    have cA₁ := continuous_ofReal.comp_continuousOn (continuousOn_in_section hS₁.cont_A hs)
    have cA₂ := continuous_ofReal.comp_continuousOn (continuousOn_in_section hS₂.cont_A hs)
    have icost : IntervalIntegrable (fun u => |e| *
        ‖(S₁.A u v : ℂ) * S₁.a u v - (S₂.A u v : ℂ) * S₂.a u v‖) volume s v :=
      ContinuousOn.intervalIntegrable_of_Icc hv.1 (continuousOn_const.mul
        ((cA₁.mul ca₁).sub (cA₂.mul ca₂)).norm)
    have hst : 0 ≤ t - s := sub_nonneg.mpr (hv.1.trans hv.2)
    have hcost u (hu : u ∈ Icc s v) : |e| *
        ‖(S₁.A u v : ℂ) * S₁.a u v - (S₂.A u v : ℂ) * S₂.a u v‖ ≤
          J * e ^ 2 * M ^ 2 * (t - s) * E := by
      have hp : (u, v) ∈ triangle s t := ⟨hu.1, hu.2, hv.2⟩
      have hso : outSeg u u v ⊆ triangle s t := by
        rintro p ⟨rfl, hx⟩
        exact ⟨hu.1, hx.1, hx.2.trans hv.2⟩
      have ha₁ : ‖S₁.a u v‖ ≤ 2 * M := by
        apply (norm_add_le _ _).trans
        have hb := add_le_add (hbox S₁ hm₁ (u, v) hp).2.2.1
          (hbox S₁ hm₁ (u, v) hp).2.2.2
        exact hb.trans (by linarith)
      have hr : S₂.r u v ≤ C * (t - s) :=
        (outgoing_radius_upper hS₂ hu.2 hso
          (fun x hx => (hbox S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).2.1)).trans
            (mul_le_mul_of_nonneg_left (show v - u ≤ t - s by linarith [hu.1, hv.2]) hC)
      have hself := potential_bound c C hc hC hS₂ hu.2 hso
        (haxis S₂ hm₂ u ⟨hu.1, hu.2.trans hv.2⟩) hM0 hε
        (fun x hx => (hbox S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).2.2.1)
        (fun x hx => (hbox S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).2.2.2)
        (fun x hx => ⟨(hbox S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).1,
          (hbox S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).2.1⟩)
        (fun x hx => (hng S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).1)
        (fun x hx => (hng S₂ hm₂ (u, x) (hso ⟨rfl, hx⟩)).2)
      have hself' : |S₂.A u v| ≤ CA * |e| * M * ε * (C * (t - s)) := by
        apply hself.trans
        exact mul_le_mul_of_nonneg_left hr (by positivity)
      have hδa := (norm_a_sub_le_distance hS₁ hS₂ hp).trans hD
      have heq : (S₁.A u v : ℂ) * S₁.a u v - (S₂.A u v : ℂ) * S₂.a u v =
          ((S₁.A u v - S₂.A u v : ℝ) : ℂ) * S₁.a u v +
            (S₂.A u v : ℂ) * (S₁.a u v - S₂.a u v) := by
        push_cast
        ring
      rw [heq]
      calc
        _ ≤ |e| * (|S₁.A u v - S₂.A u v| * ‖S₁.a u v‖ +
            |S₂.A u v| * ‖S₁.a u v - S₂.a u v‖) := by
          gcongr
          simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le
            (((S₁.A u v - S₂.A u v : ℝ) : ℂ) * S₁.a u v)
            ((S₂.A u v : ℂ) * (S₁.a u v - S₂.a u v))
        _ ≤ |e| * ((B * |e| * M * (t - s) * E) * (2 * M) +
            (CA * |e| * M * ε * (C * (t - s))) * E) := by gcongr; exact hA u v hp
        _ ≤ |e| * ((B * |e| * M * (t - s) * E) * (2 * M) +
            (CA * |e| * M ^ 2 * 1 * (C * (t - s))) * E) := by
          have hMsq : M ≤ M ^ 2 := by
            simpa only [mul_one, ← pow_two] using mul_le_mul_of_nonneg_left hM hM0
          gcongr
        _ = _ := by dsimp [J]; rw [← sq_abs e]; ring
    refine ⟨icost, ?_⟩
    have hi := intervalIntegral.integral_mono_on hv.1 icost
      (intervalIntegrable_const (c := J * e ^ 2 * M ^ 2 * (t - s) * E)) hcost
    rw [intervalIntegral.integral_const, smul_eq_mul] at hi
    calc
      _ ≤ (v - s) * (J * e ^ 2 * M ^ 2 * (t - s) * E) := hi
      _ ≤ (t - s) * (J * e ^ 2 * M ^ 2 * (t - s) * E) := by gcongr; linarith [hv.2]
      _ = (4 * J) * σ * E := by dsimp [σ]; ring
      _ ≤ K * σ * E := by
        have hJK : 4 * J ≤ K := by dsimp [K]; linarith
        gcongr

end EmcsfAcExtension.Local.Broad
