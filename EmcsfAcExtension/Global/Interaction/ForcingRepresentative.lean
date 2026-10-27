module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Renormalized
import EmcsfAcExtension.Global.Interaction.Forcing
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Global.Observation.CylinderClock

/-! # Raw envelopes dominate the selected cylinder forcing

Proper rational rectangles give a single good-label set on the original
characteristic wedge. Incoming continuity then extends the raw bounds on
countably many cylinder rows to every row, including the moving boundary.
Source: `charged_SF_new_version.tex:L3832–L3835`, approved internal project record.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Interaction

/-- [internal] Countable proper rectangles identify the selected weighted
density with the raw derivative simultaneously throughout an incoming wedge.
There are no constants or additional regularity assumptions. -/
theorem ae_weighted_representation_on_orig {ui e a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) :
    ∀ᵐ v : ℝ, v ≤ 0 → ∀ u, a ≤ u → u < v →
      weightedJ S u v = weightedJRepresentative e S a u v := by
  have hall : ∀ᵐ v : ℝ, ∀ q p : ℚ, a < (q : ℝ) →
      (q : ℝ) < p → (p : ℝ) < 0 → v ∈ Icc (p : ℝ) 0 →
      ∀ u ∈ Icc a (q : ℝ),
        weightedJ S u v = weightedJRepresentative e S a u v := by
    simp only [ae_all_iff]
    intro q p haq hqp hp
    apply (ae_restrict_iff' measurableSet_Icc).1
    apply Calculus.weighted_representation ui e S h a q p 0 haq hp
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    have huv := hu.2.trans_lt (hqp.trans_le hv.1)
    exact ⟨⟨hia.trans hu.1, huv.trans_le hv.2, huv.le, hv.2⟩, huv⟩
  filter_upwards [hall] with v hv hv0 u hau huv
  obtain ⟨p, hup, hpv⟩ := exists_rat_btwn huv
  obtain ⟨q, huq, hqp⟩ := exists_rat_btwn hup
  exact hv q p (hau.trans_lt huq) hqp (hpv.trans_le hv0)
    ⟨hpv.le, hv0⟩ u ⟨hau, huq.le⟩

/-- [internal] The prescribed weighted representative is incoming continuous
on each proper section, even on exceptional labels. Constants: none. -/
theorem continuousOn_weighted_representative_in {ui e a u v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hau : a < u)
    (huv : u < v) (hv : v ≤ 0) :
    ContinuousOn (fun x => weightedJRepresentative e S a x v) (Icc a u) := by
  have hmid : u < (u + v) / 2 ∧ (u + v) / 2 < v := ⟨by linarith, by linarith⟩
  have hrect : Icc a u ×ˢ Icc ((u + v) / 2) v ⊆
      origDomain ui ∩ {p | p.1 < p.2} := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxy := hx.2.trans_lt (hmid.1.trans_le hy.1)
    exact ⟨⟨hia.trans hx.1, hxy.trans_le (hy.2.trans hv), hxy.le, hy.2.trans hv⟩, hxy⟩
  simpa only [uIcc_of_le hau.le] using
    (Renormalized.weighted_section h.solution hau hmid.2 hrect v ⟨hmid.2.le, le_rfl⟩).1.continuousOn

/-- [internal] A raw row envelope dominates the selected representative on
one common label set for every incoming time in a cylinder's exterior.
Bounds on rational clock rows pass to every row by incoming continuity;
strictly increasing cylinder labels retain the moving boundary endpoint.
No constants depend on the data, stage duration or coupling. -/
theorem cylinder_representative_domination {ui e a b v₀ r s t : ℝ}
    {S : Fields} {vb g : ℝ → ℝ} (h : OriginalData ui e S)
    (γ : ClockCylinder S (origDomain ui) r s t) (hr : 0 < r) (hst : s ≤ t)
    (hcurve : ∀ τ ∈ Icc s t, γ.U τ ∈ Icc a b ∧ γ.V τ = vb (γ.U τ))
    (hlabels : Icc (γ.V s) (γ.V t) ⊆ Icc v₀ 0)
    (hraw : ∀ u ∈ Icc a b, ∀ᵐ v ∂volume.restrict (Icc v₀ 0),
      vb u ≤ v → ‖weightedJ S u v‖ ≤ g v) :
    ∀ᵐ v : ℝ, v ∈ Icc (γ.V s) (γ.V t) →
      ∀ u ∈ Icc (γ.U s) (γ.U t), (u, v) ∈ exteriorDomain ui a b vb →
        ‖weightedJRepresentative e S (γ.U s) u v‖ ≤ g v := by
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hrep := ae_weighted_representation_on_orig h (γ.mem s hs).1
  have hrows : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), ∀ q : ℚ,
      (q : ℝ) ∈ Icc s t → γ.V q ≤ v → ‖weightedJ S (γ.U q) v‖ ≤ g v := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Icc s t
    · exact (hraw _ (hcurve q hq).1).mono fun v hv _ hvq =>
        hv (by rwa [← (hcurve q hq).2])
    · exact ae_of_all _ fun _ hv => (hq hv).elim
  have hstart := hraw _ (hcurve s hs).1
  filter_upwards [hrep, (ae_restrict_iff' measurableSet_Icc).1 hrows,
    (ae_restrict_iff' measurableSet_Icc).1 hstart] with v hrep hrows hstart hv u hu hD
  have hv0 := (hlabels hv).2
  have hvm := hlabels hv
  have himage := γ.c1_U.continuousOn.image_Icc_of_monotoneOn hst
    (γ.strictMonoOn_U h.solution).monotoneOn
  obtain ⟨τ, hτ, rfl⟩ := (show γ.U '' Icc s t = Icc (γ.U s) (γ.U t) from himage) ▸ hu
  have hproper : γ.U τ < γ.V τ := by
    have hp := γ.mem τ hτ
    refine lt_of_le_of_ne hp.2.2.1 ?_
    intro heq
    have ha := (h.solution.axis (γ.U τ) (by simpa only [← heq] using hp)).1
    have hb := γ.radius τ hτ
    rw [← heq, ha] at hb
    exact hr.ne' hb.symm
  have hVv : γ.V τ ≤ v := by
    rw [(hcurve τ hτ).2]
    exact hD.2.2.2
  have hUv := hproper.trans_le hVv
  have hUs := (γ.strictMonoOn_U h.solution).monotoneOn hs hτ hτ.1
  rcases hτ.1.eq_or_lt with heq | hlt
  · subst τ
    rw [← hrep hv0 _ le_rfl hUv]
    exact hstart hvm (by rwa [← (hcurve s hs).2])
  · obtain ⟨q, _hqmono, hqmem, hqlim⟩ := Rat.denseRange_cast.exists_seq_strictMono_tendsto_of_lt
      (show Monotone (fun q : ℚ => (q : ℝ)) from fun _ _ hq => Rat.cast_le.mpr hq) hlt
    have hqst (n : ℕ) : (q n : ℝ) ∈ Icc s t :=
      ⟨(hqmem n).1.le, (hqmem n).2.le.trans hτ.2⟩
    have hqU (n : ℕ) : γ.U (q n) ∈ Icc (γ.U s) (γ.U τ) :=
      ⟨(γ.strictMonoOn_U h.solution).monotoneOn hs (hqst n) (hqmem n).1.le,
        (γ.strictMonoOn_U h.solution).monotoneOn (hqst n) hτ (hqmem n).2.le⟩
    have hcont := continuousOn_weighted_representative_in h (γ.mem s hs).1
      ((γ.strictMonoOn_U h.solution) hs hτ hlt) hUv hv0
    have hlimU : Tendsto (fun n => γ.U (q n)) atTop (𝓝 (γ.U τ)) :=
      (γ.c1_U.continuousOn τ hτ).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hqlim, Eventually.of_forall hqst⟩)
    have hlim := (hcont (γ.U τ) ⟨hUs, le_rfl⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlimU, Eventually.of_forall hqU⟩)
    apply le_of_tendsto hlim.norm
    apply Eventually.of_forall
    intro n
    change ‖weightedJRepresentative e S (γ.U s) (γ.U (q n)) v‖ ≤ g v
    rw [← hrep hv0 _ (hqU n).1 ((hqU n).2.trans_lt hUv)]
    exact hrows hvm (q n) (hqst n)
      (((γ.strictMonoOn_V h.solution).monotoneOn (hqst n) hτ (hqmem n).2.le).trans hVv)

/-- [node sec:charged-terminal-interaction#disjoint-cylinder-label-forcing]
The raw nonnegative L¹ row envelope bounds the selected derivative forcing
on disjoint stopped cylinders by `c⁻¹ J`. The exact coefficient depends only
on `c`, uniformly in all data, coupling, stage counts and durations.
The common representative bound is derived, including at partial endpoints. -/
theorem disjoint_cylinder_label_forcing_of_raw_envelope (c : ℝ) (hc : 0 < c)
    {ui e a b δ Λ F ε v₀ : ℝ} {S : Fields} {vb g : ℝ → ℝ}
    (h : OriginalData ui e S)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (N : ℕ) (r s t : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (r n) (s n) (t n))
    (hr : ∀ n, 0 < r n) (hst : ∀ n, s n ≤ t n)
    (hcurve : ∀ n, ∀ τ ∈ Icc (s n) (t n),
      (γ n).U τ ∈ Icc a b ∧ (γ n).V τ = vb ((γ n).U τ))
    (hv₀ : v₀ ≤ 0)
    (hlabels : ∀ n, Icc ((γ n).V (s n)) ((γ n).V (t n)) ⊆ Icc v₀ 0)
    (hdisj : Pairwise fun n m => Disjoint
      (Ioc ((γ n).V (s n)) ((γ n).V (t n)))
      (Ioc ((γ m).V (s m)) ((γ m).V (t m))))
    (hg : IntegrableOn g (Icc v₀ 0))
    (hg0 : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), 0 ≤ g v)
    (hraw : ∀ u ∈ Icc a b, ∀ᵐ v ∂volume.restrict (Icc v₀ 0),
      vb u ≤ v → ‖weightedJ S u v‖ ≤ g v) :
    (∑ n, ∫⁻ τ in Icc (s n) (t n), ENNReal.ofReal
      (‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
        S.lam ((γ n).U τ) ((γ n).V τ) ^ 2)) ≤
      ENNReal.ofReal (c⁻¹ * ∫ v in v₀..0, g v) := by
  have hp n τ (hτ : τ ∈ Icc (s n) (t n)) :
      ((γ n).U τ, (γ n).V τ) ∈ exteriorDomain ui a b vb :=
    ⟨(γ n).mem τ hτ, (hcurve n τ hτ).1.1, (hcurve n τ hτ).1.2,
      (hcurve n τ hτ).2.ge⟩
  have hb := disjoint_cylinder_label_forcing c hc h.solution N r s t γ hr hst v₀
    (fun v => ENNReal.ofReal (g v)) (exteriorDomain ui a b vb) hp hlabels hdisj
    (fun n τ hτ => (hstop _ (hp n τ hτ)).2.2.1)
    (fun n => (cylinder_representative_domination h (γ n) (hr n) (hst n)
      (hcurve n) (hlabels n) hraw).mono fun v hv hm u hu hD =>
        ENNReal.ofReal_le_ofReal (hv hm u hu hD))
  have hJ : ENNReal.ofReal (∫ v in v₀..0, g v) =
      ∫⁻ v in Icc v₀ 0, ENNReal.ofReal (g v) := by
    rw [intervalIntegral.integral_of_le hv₀, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal hg hg0
  rwa [← hJ, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] at hb

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

open Interaction

/-- [node eq:ct-forcing]
Total covariant cylinder forcing from the recorded stopped-boundary budgets
and the raw L¹ row envelope. The representative domination is proved from
`OriginalData`, fixed-density representation and incoming continuity.
The positive constant depends only on `δ, F`, before all solution data,
coupling, scales, stage counts and durations; the electric cost is `C ζ²`. -/
theorem ct_forcing_of_raw_envelope (δ F : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hF : 0 ≤ F) (hF1 : F < 1) :
    ∃ C > 0, ∀ (c Λ ε : ℝ), 0 < c → ∀ (ui e a b v₀ H Jstop : ℝ) (S : Fields) (vb g : ℝ → ℝ),
      OriginalData ui e S → a ≤ b → ContinuousOn vb (Icc a b) → 0 ≤ Jstop →
      (∀ u ∈ Icc a b, (u, vb u) ∈ origDomain ui) →
      (∀ u ∈ Icc a b, u < vb u ∧ v₀ ≤ vb u) →
      ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u 0‖ ≤ H) →
      IntegrableOn g (Icc v₀ 0) →
      (∀ᵐ w ∂volume.restrict (Icc v₀ 0), 0 ≤ g w) →
      (∀ u ∈ Icc a b, ∀ᵐ w ∂volume.restrict (Icc v₀ 0),
        vb u ≤ w → ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v₀..0, g w) ≤ Jstop →
      ∀ (N : ℕ) (r s t E : Fin N → ℝ)
        (γ : ∀ n, ClockCylinder S (origDomain ui) (r n) (s n) (t n)),
      (∀ n, 0 < r n) → (∀ n, s n ≤ t n) →
      (∀ n, 0 ≤ E n ∧ E n ≤ F ^ 2) →
      (∀ n, ∀ τ ∈ Icc (s n) (t n),
        (γ n).U τ ∈ Icc a b ∧ (γ n).V τ = vb ((γ n).U τ)) →
      (Pairwise fun n m => Disjoint
        (Ioc ((γ n).U (s n)) ((γ n).U (t n)))
        (Ioc ((γ m).U (s m)) ((γ m).U (t m)))) →
      (Pairwise fun n m => Disjoint
        (Ioc ((γ n).V (s n)) ((γ n).V (t n)))
        (Ioc ((γ m).V (s m)) ((γ m).V (t m)))) →
      (∀ n, ∀ τ ∈ Icc (s n) (t n),
        S.m ((γ n).U τ) ((γ n).V τ) / r n +
          ‖S.theta ((γ n).U τ) ((γ n).V τ) / S.lam ((γ n).U τ) ((γ n).V τ)‖ ^ 2 ≤ E n) →
      (∀ n, (∫ τ in s n..t n,
        (‖S.theta ((γ n).U τ) ((γ n).V τ) / S.lam ((γ n).U τ) ((γ n).V τ)‖ ^ 2 +
         ‖S.xi ((γ n).U τ) ((γ n).V τ) / S.nu ((γ n).U τ) ((γ n).V τ)‖ ^ 2 +
         S.mu ((γ n).U τ) ((γ n).V τ) ^ 2) / r n) ≤ E n) →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      (∑ n, ∫ τ in s n..t n,
        ‖deriv (fun x => S.a ((γ n).U x) ((γ n).V x)) τ +
          I * e * S.A ((γ n).U τ) ((γ n).V τ) * deriv (γ n).U τ *
            S.a ((γ n).U τ) ((γ n).V τ)‖) ≤
        c⁻¹ * (∫ v in v₀..0, g v) + C * (∑ n, E n) +
          C * (e ^ 2 * M₀ ^ 2 * S.r a 0 ^ 2) := by
  obtain ⟨C, hC, hforcing⟩ := ct_forcing δ F hδ hδ1 hF hF1
  refine ⟨C, hC, ?_⟩
  intro c Λ ε hc ui e a b v₀ H Jstop S vb g h hab hcont hJstop hmem hproper hstop hcore
    hterm hg hg0 hraw hJ N r s t E γ hr hst hE hcurve hdisjU hdisjV hbudget hquad
  apply hforcing c Λ ε hc ui e a b v₀ H Jstop S vb g h hab hcont hJstop hmem hproper
    hstop hcore hterm hg hg0 hraw hJ N r s t E γ hr hst hE hcurve hdisjU hdisjV hbudget hquad
  intro n
  apply cylinder_representative_domination h (γ n) (hr n) (hst n) (hcurve n) ?_ hraw
  intro v hv
  have hs : s n ∈ Icc (s n) (t n) := ⟨le_rfl, hst n⟩
  have ht : t n ∈ Icc (s n) (t n) := ⟨hst n, le_rfl⟩
  refine ⟨?_, hv.2.trans ((γ n).mem (t n) ht).2.2.2⟩
  have hstart := (hproper _ (hcurve n (s n) hs).1).2
  rw [← (hcurve n (s n) hs).2] at hstart
  exact hstart.trans hv.1

end EmcsfAcExtension.Global
