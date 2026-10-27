module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Renormalized
import EmcsfAcExtension.Global.Interaction.ConnectorScalar
import EmcsfAcExtension.Global.Interaction.BoundaryCharge
import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Interaction.BoundaryChain
import EmcsfAcExtension.Global.Observation.CylinderIdentity
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Infra.Density.CurveChain
import EmcsfAcExtension.Infra.Level.Substitution
import EmcsfAcExtension.Local.Calculus.Sections

/-! # Boundary forcing and its terminal radius moment

All clock integrals use `dτ = (-ν_b) du`. The terminal moment is the
primitive `-R²/2`, so its bound does not involve cylinder duration or a
cooling energy. Source: `charged_SF_new_version.tex:L3817–L3835`, approved internal project record.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Interaction

/-- [node sec:charged-terminal-interaction#boundary-terminal-clock-comparison]
Along the whole stopped boundary, including partial cylinders and incoming
connectors, the boundary radius and clock density are bounded by their
terminal values. Constants: none. -/
theorem boundary_terminal_clock_comparison {ui e a b δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} (hS : IsSolution e S (origDomain ui))
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hmem : ∀ u ∈ Icc a b, (u, vb u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < vb u) :
    ∀ u ∈ Icc a b, S.r u (vb u) ≤ S.r u 0 ∧ -S.nu u (vb u) ≤ -S.nu u 0 := by
  intro u hu
  have hp := hmem u hu
  have hs : outSeg u (vb u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    change x = u at hx
    subst x
    exact ⟨hp.1, hp.2.1, (hproper u hu).le.trans hv.1, hv.2⟩
  refine ⟨Gap.radius_out_le hS (hproper u hu).le hp.2.2.2 hs, ?_⟩
  apply neg_le_neg
  apply Gap.nu_out_antitone_of_charge_bound hS (hproper u hu) hp.2.2.2 hs
  intro v hv
  have hpv : (u, v) ∈ exteriorDomain ui a b vb := ⟨hs ⟨rfl, hv⟩, hu.1, hu.2, hv.1⟩
  have hh := hstop (u, v) hpv
  linarith only [hh.1, hh.2.2.2.2.2.2]

/-- [node sec:charged-terminal-interaction#boundary-clock-moment]
The full or partial stopped boundary has radius moment at most `R(a)²/2`.
The exact coefficient `1/2` is uniform in all solution, coupling, stage,
duration and energy parameters; no inverse energy occurs. -/
theorem boundary_clock_moment {ui e a b δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} (hS : IsSolution e S (origDomain ui))
    (hab : a ≤ b) (hcont : ContinuousOn vb (Icc a b))
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hmem : ∀ u ∈ Icc a b, (u, vb u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < vb u) :
    (∫ u in a..b, S.r u (vb u) * (-S.nu u (vb u))) ≤ S.r a 0 ^ 2 / 2 := by
  have hb := hmem b ⟨hab, le_rfl⟩
  have ha := hmem a ⟨le_rfl, hab⟩
  have hs : inSeg a b 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨hu, hub, rfl⟩
    exact ⟨ha.1.trans hu, hub.trans_lt hb.2.1, (hub.trans_lt hb.2.1).le, le_rfl⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cbr := hS.cont_r.comp (continuousOn_id.prodMk hcont) hmem
  have cbn := hS.cont_nu.comp (continuousOn_id.prodMk hcont) hmem
  have hi := (cr.mul cn.neg).intervalIntegrable_of_Icc (μ := volume) hab
  have hr := Local.IsSolution.in_section hS hab hb.2.1 hs
  have hac := (hr.1.1.mul hr.1.1).const_mul (-1 / 2 : ℝ)
  have hd : ∀ᵐ u ∂volume.restrict (Icc a b),
      HasDerivAt (fun x => (-1 / 2 : ℝ) * (S.r x 0 * S.r x 0))
        (S.r u 0 * (-S.nu u 0)) u := by
    filter_upwards [hr.1.2] with u hu
    exact ((hu.mul hu).const_mul (-1 / 2 : ℝ)).congr_deriv (by ring)
  have hd' : ∀ᵐ u : ℝ, u ∈ uIcc a b →
      HasDerivAt (fun x => (-1 / 2 : ℝ) * (S.r x 0 * S.r x 0))
        (S.r u 0 * (-S.nu u 0)) u := by
    rw [uIcc_of_le hab]
    exact (ae_restrict_iff' measurableSet_Icc).1 hd
  have heq := hac.integral_eq_sub_of_ae_hasDerivAt_normed hi hd'
  have hcmp := intervalIntegral.integral_mono_on hab
    ((cbr.mul cbn.neg).intervalIntegrable_of_Icc (μ := volume) hab) hi (fun u hu => by
      obtain ⟨hrle, hnle⟩ := boundary_terminal_clock_comparison hS hstop hmem hproper u hu
      exact mul_le_mul hrle hnle
        (neg_pos.mpr (hS.nu_neg _ (hmem u hu))).le
        (hS.r_pos (u, 0) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hb.2.1)).le)
  rw [heq] at hcmp
  dsimp only [Pi.mul_apply, Pi.neg_apply, Function.comp_apply, Function.uncurry, id_eq] at hcmp
  nlinarith only [hcmp, sq_nonneg (S.r b 0)]

/-- [node sec:charged-terminal-interaction#scalar-mass-boundary-forcing]
The cubic and geometric forcing on finitely many proper cylinders is
bounded by the sum of their given quadratic budgets. The constant is
chosen from `δ, F` before every solution, radius, energy and duration.
This conditional use of stage budgets is exactly the source premise;
it does not invoke a completed observation window. -/
theorem scalar_mass_boundary_forcing (δ F : ℝ) (hδ : 0 < δ) (hF : 0 ≤ F) :
    ∃ C > 0, ∀ (ui e : ℝ) (S : Fields) (_hS : IsSolution e S (origDomain ui))
      (N : ℕ) (r s t E : Fin N → ℝ)
      (γ : ∀ n, ClockCylinder S (origDomain ui) (r n) (s n) (t n)),
      (∀ n, 0 < r n) → (∀ n, s n ≤ t n) →
      (∀ n, ∀ τ ∈ Icc (s n) (t n),
        0 ≤ S.mu ((γ n).U τ) ((γ n).V τ) ∧
        δ ≤ 1 - S.mu ((γ n).U τ) ((γ n).V τ) ∧
        S.Q ((γ n).U τ) ((γ n).V τ) ^ 2 / r n ^ 2 ≤
          S.mu ((γ n).U τ) ((γ n).V τ) ∧
        ‖S.theta ((γ n).U τ) ((γ n).V τ) /
          (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ≤ F) →
      (∀ n, (∫ τ in s n..t n,
        (‖S.theta ((γ n).U τ) ((γ n).V τ) /
              (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
          ‖S.xi ((γ n).U τ) ((γ n).V τ) /
              (S.nu ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 2 +
          S.mu ((γ n).U τ) ((γ n).V τ) ^ 2) / r n) ≤ E n) →
      (∑ n, ∫ τ in s n..t n,
        (‖S.theta ((γ n).U τ) ((γ n).V τ) /
            (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖ ^ 3 +
          ((S.mu ((γ n).U τ) ((γ n).V τ) -
              S.Q ((γ n).U τ) ((γ n).V τ) ^ 2 / r n ^ 2) /
            (1 - S.mu ((γ n).U τ) ((γ n).V τ))) *
          ‖S.theta ((γ n).U τ) ((γ n).V τ) /
            (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖) / r n) ≤ C * ∑ n, E n := by
  let C : ℝ := F + 1 / (2 * δ)
  have hC : 0 < C := add_pos_of_nonneg_of_pos hF (by positivity)
  refine ⟨C, hC, ?_⟩
  intro ui e S hS N r s t E γ hr hst hbound hbudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨cy, cz, cm⟩ := Cylinder.continuousOn_normalized_traces hS (γ n)
  have cQ := (γ n).continuousOn_trace hS.cont_Q
  let y := fun τ => ‖S.theta ((γ n).U τ) ((γ n).V τ) /
    (S.lam ((γ n).U τ) ((γ n).V τ) : ℂ)‖
  let z := fun τ => ‖S.xi ((γ n).U τ) ((γ n).V τ) /
    (S.nu ((γ n).U τ) ((γ n).V τ) : ℂ)‖
  let m := fun τ => S.mu ((γ n).U τ) ((γ n).V τ)
  let q := fun τ => S.Q ((γ n).U τ) ((γ n).V τ) ^ 2 / r n ^ 2
  have cκ := (cm.sub ((cQ.pow 2).div_const (r n ^ 2))).div
    (continuousOn_const.sub cm) (fun τ hτ => (hδ.trans_le (hbound n τ hτ).2.1).ne')
  have ci := (((cy.norm.pow 3).add (cκ.mul cy.norm)).div_const (r n)).intervalIntegrable_of_Icc
    (μ := volume) (hst n)
  have cb := ((((cy.norm.pow 2).add (cz.norm.pow 2)).add (cm.pow 2)).div_const
    (r n)).intervalIntegrable_of_Icc (μ := volume) (hst n)
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc (s n) (t n)) :
      (y τ ^ 3 + ((m τ - q τ) / (1 - m τ)) * y τ) / r n ≤
        C * ((y τ ^ 2 + z τ ^ 2 + m τ ^ 2) / r n) := by
    obtain ⟨hm, hg, _hq, hy⟩ := hbound n τ hτ
    have hy0 : 0 ≤ y τ := norm_nonneg _
    have hq0 : 0 ≤ q τ := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hκ : (m τ - q τ) / (1 - m τ) ≤ m τ / δ :=
      (div_le_div_of_nonneg_right (sub_le_self _ hq0) (hδ.le.trans hg)).trans
        (div_le_div_of_nonneg_left hm hδ hg)
    have hκy := mul_le_mul_of_nonneg_right hκ hy0
    have hyoung : m τ / δ * y τ ≤ (m τ ^ 2 + y τ ^ 2) / (2 * δ) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * δ)).2
      have he : m τ / δ * y τ * (2 * δ) = 2 * m τ * y τ := by field_simp
      rw [he]
      nlinarith only [sq_nonneg (m τ - y τ)]
    have hcubic : y τ ^ 3 ≤ F * y τ ^ 2 := by
      simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_right hy (sq_nonneg (y τ))
    have hrest : 0 ≤ F * (z τ ^ 2 + m τ ^ 2) + z τ ^ 2 / (2 * δ) := by positivity
    have htotal : y τ ^ 3 + ((m τ - q τ) / (1 - m τ)) * y τ ≤
        C * (y τ ^ 2 + z τ ^ 2 + m τ ^ 2) := by
      calc
        _ ≤ F * y τ ^ 2 + (m τ ^ 2 + y τ ^ 2) / (2 * δ) :=
          add_le_add hcubic (hκy.trans hyoung)
        _ ≤ C * (y τ ^ 2 + z τ ^ 2 + m τ ^ 2) := by
          have he : C * (y τ ^ 2 + z τ ^ 2 + m τ ^ 2) -
              (F * y τ ^ 2 + (m τ ^ 2 + y τ ^ 2) / (2 * δ)) =
              F * (z τ ^ 2 + m τ ^ 2) + z τ ^ 2 / (2 * δ) := by
            dsimp only [C]
            ring
          exact sub_nonneg.mp (he.symm ▸ hrest)
    calc
      _ ≤ C * (y τ ^ 2 + z τ ^ 2 + m τ ^ 2) / r n :=
        div_le_div_of_nonneg_right htotal (hr n).le
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on (hst n) ci (cb.const_mul C) hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (hbudget n) hC.le)

/-- [internal]
The selected derivative forcing on cylinders with disjoint label interiors
is at most `c⁻¹` times the incoming-label envelope. The envelope is imposed
on one full-measure label set before all incoming times, then pulled back
using the actual bi-Lipschitz label map. The nonnegative formulation also
allows infinite envelopes; a finite source envelope gives the stated bound.
The exact coefficient depends only on `c`, before every solution and stage. -/
theorem disjoint_cylinder_label_forcing (c : ℝ) (hc : 0 < c)
    {ui e : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (N : ℕ) (r s t : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (r n) (s n) (t n))
    (_hr : ∀ n, 0 < r n) (hst : ∀ n, s n ≤ t n)
    (v₀ : ℝ) (g : ℝ → ℝ≥0∞) (D : Set (ℝ × ℝ))
    (hcurve : ∀ n, ∀ τ ∈ Icc (s n) (t n), ((γ n).U τ, (γ n).V τ) ∈ D)
    (hlabels : ∀ n, Icc ((γ n).V (s n)) ((γ n).V (t n)) ⊆ Icc v₀ 0)
    (hdisj : Pairwise fun n m => Disjoint
      (Ioc ((γ n).V (s n)) ((γ n).V (t n)))
      (Ioc ((γ m).V (s m)) ((γ m).V (t m))))
    (hlam : ∀ n, ∀ τ ∈ Icc (s n) (t n), c ≤ S.lam ((γ n).U τ) ((γ n).V τ))
    (hmajorant : ∀ n, ∀ᵐ v : ℝ,
      v ∈ Icc ((γ n).V (s n)) ((γ n).V (t n)) →
      ∀ u ∈ Icc ((γ n).U (s n)) ((γ n).U (t n)), (u, v) ∈ D →
        ENNReal.ofReal ‖weightedJRepresentative e S ((γ n).U (s n)) u v‖ ≤ g v) :
    (∑ n, ∫⁻ τ in Icc (s n) (t n), ENNReal.ofReal
      (‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
        S.lam ((γ n).U τ) ((γ n).V τ) ^ 2)) ≤
      ENNReal.ofReal (c⁻¹) * ∫⁻ v in Icc v₀ 0, g v := by
  have hstage (n : Fin N) :
      (∫⁻ τ in Icc (s n) (t n), ENNReal.ofReal
        (‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
          S.lam ((γ n).U τ) ((γ n).V τ) ^ 2)) ≤
        ENNReal.ofReal (c⁻¹) * ∫⁻ v in Ioc ((γ n).V (s n)) ((γ n).V (t n)), g v := by
    obtain ⟨KU, KV, LU, LV, hU, hV, hUa, hVa⟩ := (γ n).exists_biLipschitz_labels hS
    have hpull := Density.ae_pullback_of_antilipschitzOn measurableSet_Icc hVa (hmajorant n)
    have hchange := Level.lintegral_image_mono measurableSet_Icc
      (γ n).rate_V ((γ n).strictMonoOn_V hS).monotoneOn g
    rw [((γ n).c1_V.continuousOn.image_Icc_of_monotoneOn (hst n)
      ((γ n).strictMonoOn_V hS).monotoneOn)] at hchange
    have himage : (∫⁻ v in Ioc ((γ n).V (s n)) ((γ n).V (t n)), g v) =
        ∫⁻ τ in Icc (s n) (t n),
          ENNReal.ofReal ((S.lam ((γ n).U τ) ((γ n).V τ))⁻¹) * g ((γ n).V τ) := by
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      exact hchange
    rw [himage, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hpull, ae_restrict_mem measurableSet_Icc] with τ hgood hτ
    have hvm : (γ n).V τ ∈ Icc ((γ n).V (s n)) ((γ n).V (t n)) :=
      ⟨((γ n).strictMonoOn_V hS).monotoneOn ⟨le_rfl, hst n⟩ hτ hτ.1,
        ((γ n).strictMonoOn_V hS).monotoneOn hτ ⟨hst n, le_rfl⟩ hτ.2⟩
    have hum : (γ n).U τ ∈ Icc ((γ n).U (s n)) ((γ n).U (t n)) :=
      ⟨((γ n).strictMonoOn_U hS).monotoneOn ⟨le_rfl, hst n⟩ hτ hτ.1,
        ((γ n).strictMonoOn_U hS).monotoneOn hτ ⟨hst n, le_rfl⟩ hτ.2⟩
    have hp := (γ n).mem τ hτ
    have hW := hgood hvm _ hum (hcurve n τ hτ)
    have hl := hS.lam_pos _ hp
    have hcoeff : ENNReal.ofReal ((S.lam ((γ n).U τ) ((γ n).V τ))⁻¹) ≤
        ENNReal.ofReal (c⁻¹) :=
      ENNReal.ofReal_le_ofReal ((inv_le_inv₀ hl hc).2 (hlam n τ hτ))
    rw [show ‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
        S.lam ((γ n).U τ) ((γ n).V τ) ^ 2 =
        (S.lam ((γ n).U τ) ((γ n).V τ))⁻¹ *
          ((S.lam ((γ n).U τ) ((γ n).V τ))⁻¹ *
            ‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖) by
          simp only [pow_two, div_eq_mul_inv, mul_inv_rev]; ring,
      ENNReal.ofReal_mul (inv_nonneg.mpr hl.le), ENNReal.ofReal_mul (inv_nonneg.mpr hl.le)]
    exact mul_le_mul' hcoeff (mul_le_mul' le_rfl hW)
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.univ) => hstage n)
  rw [← Finset.mul_sum] at hsum
  have hUnion := lintegral_iUnion (μ := volume) (fun n : Fin N =>
    measurableSet_Ioc (a := (γ n).V (s n)) (b := (γ n).V (t n))) hdisj g
  rw [tsum_fintype] at hUnion
  rw [← hUnion] at hsum
  apply hsum.trans
  apply mul_le_mul' le_rfl
  apply lintegral_mono_set
  intro v hv
  obtain ⟨n, hn⟩ := mem_iUnion.mp hv
  exact hlabels n (Ioc_subset_Icc_self hn)

/-- [node sec:charged-terminal-interaction#boundary-electric-pointwise]
Electric boundary forcing from the stopped row and its source-defined
scalar envelope. The positive constant depends only on the complete-core
gap `δ`, before all solution data, scalar backgrounds, scales and labels.
No scalar or charge profile is assumed as a replacement for its proof. -/
theorem boundary_electric_pointwise (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C > 0, ∀ (e c F Jstop H : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a v : ℝ) (g : ℝ → ℝ),
      IsSolution e S D → u < a → a ≤ v → v ≤ 0 → outSeg u u 0 ⊆ D →
      0 < c → 0 ≤ F → F < 1 → 0 ≤ Jstop →
      (∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ w ∈ Icc a 0, c ≤ S.lam u w) →
      (∀ w ∈ Icc a 0, ‖S.theta u w / S.lam u w‖ ≤ F) →
      S.m u a / S.r u a ≤ F ^ 2 → ‖S.phi u 0‖ ≤ H →
      IntervalIntegrable g volume a 0 →
      (∀ᵐ w ∂volume.restrict (Icc a 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in a..0, g w) ≤ Jstop →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      ‖I * (e : ℂ) * S.Q u v * S.phi u v /
        (((1 - S.mu u v) * S.r u v : ℝ) : ℂ)‖ ≤ C * e ^ 2 * M₀ ^ 2 * F * S.r u v := by
  obtain ⟨C, hC, hcharge⟩ := ct_charge_profile_of_scalar_bound δ hδ hδ1
  refine ⟨C / δ, by positivity, ?_⟩
  intro e c F Jstop H S D u a v g hS hua hav hv hs hc hF hF1 hJstop
    hgap hl hy hbudget hterm hg hmajor hJ
  let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
  have ha0 := hav.trans hv
  have hrow : outSeg u a 0 ⊆ D := fun p hp => hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hphi := ct_m0_of_row_envelope hS hua ha0 hrow hc hF hF1
    hl hy hterm g hg hmajor hJ
  have hH : 0 ≤ H := (norm_nonneg _).trans hterm
  have hden : 0 < 1 - F ^ 2 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hM : 1 ≤ M₀ := by
    have hh : 0 ≤ H + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by positivity
    dsimp only [M₀]; linarith only [hh]
  have hq := hcharge e M₀ F S D u a v hS hua hav
    (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hv⟩) hM hF hF1.le
    (fun w hw => hgap w ⟨hw.1, hw.2.trans hv⟩)
    (fun w hw => hphi w ⟨hw.1, hw.2.trans hv⟩)
    (fun w hw => hy w ⟨hw.1, hw.2.trans hv⟩) hbudget
  have hq' : |S.Q u v| / S.r u v ^ 2 ≤ C * |e| * M₀ * Real.sqrt (F ^ 2) := by
    simpa only [Real.sqrt_sq hF] using hq
  have he := electric_forcing_of_profiles hδ hC.le (by linarith only [hM] : 0 ≤ M₀)
    (hS.r_pos (u, v) (hs ⟨rfl, (hua.trans_le hav).le, hv⟩) (hua.trans_le hav))
    (hgap v ⟨(hua.trans_le hav).le, hv⟩) (hphi v ⟨hav, hv⟩) hq'
  simpa only [Real.sqrt_sq hF] using he

/-- [internal] The sum of cylinder radius moments is controlled by the full
boundary moment. Disjoint incoming intervals allow connectors and partial
stages between cylinders. The exact coefficient `1/2` is independent of
stage count, duration, radii and energies. -/
theorem cylinder_radius_moment_sum {ui e a b δ c Λ F ε : ℝ}
    {S : Fields} {vb : ℝ → ℝ} (hS : IsSolution e S (origDomain ui))
    (hab : a ≤ b) (hcont : ContinuousOn vb (Icc a b))
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hmem : ∀ u ∈ Icc a b, (u, vb u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < vb u)
    (N : ℕ) (r s t : Fin N → ℝ)
    (γ : ∀ n, ClockCylinder S (origDomain ui) (r n) (s n) (t n))
    (hr : ∀ n, 0 < r n) (hst : ∀ n, s n ≤ t n)
    (hcurve : ∀ n, ∀ τ ∈ Icc (s n) (t n),
      (γ n).U τ ∈ Icc a b ∧ (γ n).V τ = vb ((γ n).U τ))
    (hdisj : Pairwise fun n m => Disjoint
      (Ioc ((γ n).U (s n)) ((γ n).U (t n)))
      (Ioc ((γ m).U (s m)) ((γ m).U (t m)))) :
    (∑ n, ∫ _τ in s n..t n, r n) ≤ S.r a 0 ^ 2 / 2 := by
  let f := fun u => S.r u (vb u) * (-S.nu u (vb u))
  have cf : ContinuousOn f (Icc a b) :=
    (hS.cont_r.comp (continuousOn_id.prodMk hcont) hmem).mul
      (hS.cont_nu.comp (continuousOn_id.prodMk hcont) hmem).neg
  have f0 u (hu : u ∈ Icc a b) : 0 ≤ f u :=
    mul_nonneg (hS.r_pos _ (hmem u hu) (hproper u hu)).le
      (neg_pos.mpr (hS.nu_neg _ (hmem u hu))).le
  have hstage (n : Fin N) : ENNReal.ofReal (∫ τ in s n..t n, r n) =
      ∫⁻ u in Ioc ((γ n).U (s n)) ((γ n).U (t n)), ENNReal.ofReal (f u) := by
    have he := Level.lintegral_image_mono measurableSet_Icc (γ n).rate_U
      ((γ n).strictMonoOn_U hS).monotoneOn (fun u => ENNReal.ofReal (f u))
    rw [(γ n).c1_U.continuousOn.image_Icc_of_monotoneOn (hst n)
      ((γ n).strictMonoOn_U hS).monotoneOn] at he
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc, he,
      ofReal_interval_integral (hst n) intervalIntegrable_const (fun _ _ => (hr n).le)]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro τ hτ
    obtain ⟨hu, hv⟩ := hcurve n τ hτ
    have hn := neg_pos.mpr (hS.nu_neg _ ((γ n).mem τ hτ))
    change ENNReal.ofReal (r n) =
      ENNReal.ofReal ((-S.nu ((γ n).U τ) ((γ n).V τ))⁻¹) * ENNReal.ofReal (f ((γ n).U τ))
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hn.le)]
    congr 1
    dsimp only [f]
    rw [← hv, (γ n).radius τ hτ]
    field_simp [(hS.nu_neg _ ((γ n).mem τ hτ)).ne]
  have hsum : ENNReal.ofReal (∑ n, ∫ τ in s n..t n, r n) =
      ∫⁻ u in ⋃ n, Ioc ((γ n).U (s n)) ((γ n).U (t n)), ENNReal.ofReal (f u) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      intervalIntegral.integral_nonneg (hst n) (fun _ _ => (hr n).le))]
    simp_rw [hstage]
    symm
    simpa only [tsum_fintype] using lintegral_iUnion (μ := volume)
      (fun n : Fin N => measurableSet_Ioc (a := (γ n).U (s n)) (b := (γ n).U (t n)))
      hdisj (fun u => ENNReal.ofReal (f u))
  have hsub : (⋃ n, Ioc ((γ n).U (s n)) ((γ n).U (t n))) ⊆ Icc a b := by
    intro u hu
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    exact ⟨(hcurve n (s n) ⟨le_rfl, hst n⟩).1.1.trans hn.1.le,
      hn.2.trans (hcurve n (t n) ⟨hst n, le_rfl⟩).1.2⟩
  have hbound := (lintegral_mono_set (f := fun u => ENNReal.ofReal (f u)) hsub).trans
    (show (∫⁻ u in Icc a b, ENNReal.ofReal (f u)) ≤ ENNReal.ofReal (S.r a 0 ^ 2 / 2) by
      rw [← ofReal_interval_integral hab (cf.intervalIntegrable_of_Icc hab) f0]
      exact ENNReal.ofReal_le_ofReal (boundary_clock_moment hS hab hcont hstop hmem hproper))
  rw [← hsum] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

open Interaction

/-- [internal]
Total covariant forcing on any finite family of cylinders on the stopped
boundary. Their disjoint incoming and outgoing label interiors include
partial stages and intervening connectors. The source scalar envelope is
derived from its row hypotheses. The positive constant depends only on
`δ, F`, before all data, scales, energies, stage counts and durations.
The electric contribution is `C ζ²`, with no inverse cooling energy. -/
theorem ct_forcing (δ F : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
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
      (∀ n, ∀ᵐ v : ℝ, v ∈ Icc ((γ n).V (s n)) ((γ n).V (t n)) →
        ∀ u ∈ Icc ((γ n).U (s n)) ((γ n).U (t n)),
          (u, v) ∈ exteriorDomain ui a b vb →
            ‖weightedJRepresentative e S ((γ n).U (s n)) u v‖ ≤ g v) →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      (∑ n, ∫ τ in s n..t n,
        ‖deriv (fun x => S.a ((γ n).U x) ((γ n).V x)) τ +
          I * e * S.A ((γ n).U τ) ((γ n).V τ) * deriv (γ n).U τ *
            S.a ((γ n).U τ) ((γ n).V τ)‖) ≤
        c⁻¹ * (∫ v in v₀..0, g v) + C * (∑ n, E n) +
          C * (e ^ 2 * M₀ ^ 2 * S.r a 0 ^ 2) := by
  obtain ⟨Cn, hCn, hneutral⟩ := scalar_mass_boundary_forcing δ F hδ hF
  obtain ⟨Cq, hCq, hcharge⟩ := ct_charge_profile_of_scalar_bound δ hδ hδ1
  let Ce := Cq / δ
  let C := 1 + Cn + Ce * F / 2
  refine ⟨C, by dsimp only [C, Ce]; positivity, ?_⟩
  intro c Λ ε hc ui e a b v₀ H Jstop S vb g h hab hcont hJstop hmem hproper hstop hcore
    hterm hg hg0 hraw hJ N r s t E γ hr hst hE hcurve hdisjU hdisjV hbudget hquad hmajor
  let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
  have hphi := scalar_profile_of_stops h hc hF hF1
    (fun u hu => ⟨(hmem u hu).1, (hproper u hu).1, (hmem u hu).2.2.2, (hproper u hu).2⟩)
    hstop hterm hg hg0 hraw hJ
  have hH : 0 ≤ H := (norm_nonneg _).trans (hterm a ⟨le_rfl, hab⟩)
  have hden : 0 < 1 - F ^ 2 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hM : 1 ≤ M₀ := by
    have hh : 0 ≤ H + (F + c⁻¹ * Jstop) / (1 - F ^ 2) := by positivity
    dsimp only [M₀]; linarith only [hh]
  have hp n τ (hτ : τ ∈ Icc (s n) (t n)) :
      ((γ n).U τ, (γ n).V τ) ∈ exteriorDomain ui a b vb :=
    ⟨(γ n).mem τ hτ, (hcurve n τ hτ).1.1, (hcurve n τ hτ).1.2,
      (hcurve n τ hτ).2.ge⟩
  have hq n τ (hτ : τ ∈ Icc (s n) (t n)) :
      S.Q ((γ n).U τ) ((γ n).V τ) ^ 2 / r n ^ 2 ≤ S.mu ((γ n).U τ) ((γ n).V τ) := by
    have hh := hstop _ (hp n τ hτ)
    have hhalf : S.Q ((γ n).U τ) ((γ n).V τ) ^ 2 / r n ^ 2 ≤
        S.mu ((γ n).U τ) ((γ n).V τ) / 2 := by
      simpa only [(γ n).radius τ hτ] using hh.2.2.2.2.2.2
    linarith only [hh.1, hhalf]
  have hnb := hneutral ui e S h.solution N r s t E γ hr hst
    (fun n τ hτ => ⟨(hstop _ (hp n τ hτ)).1, (hstop _ (hp n τ hτ)).2.1,
      hq n τ hτ, (hstop _ (hp n τ hτ)).2.2.2.2.1⟩) hquad
  have hfi n := cylinder_forcing_integrals h.solution (γ n) (hr n) (hst n) (hq n)
  have hlabel n : Icc ((γ n).V (s n)) ((γ n).V (t n)) ⊆ Icc v₀ 0 := by
    intro v hv
    exact ⟨((hproper _ (hcurve n (s n) ⟨le_rfl, hst n⟩).1).2.trans
      (by rw [← (hcurve n (s n) ⟨le_rfl, hst n⟩).2]; exact hv.1)),
      hv.2.trans ((γ n).mem (t n) ⟨hst n, le_rfl⟩).2.2.2⟩
  have hd := disjoint_cylinder_label_forcing c hc h.solution N r s t γ hr hst v₀
    (fun v => ENNReal.ofReal (g v)) (exteriorDomain ui a b vb) hp hlabel hdisjV
    (fun n τ hτ => (hstop _ (hp n τ hτ)).2.2.1)
    (fun n => (hmajor n).mono fun v hv hm u hu hD => ENNReal.ofReal_le_ofReal (hv hm u hu hD))
  have hv₀ : v₀ ≤ 0 := (hproper a ⟨le_rfl, hab⟩).2.trans (hmem a ⟨le_rfl, hab⟩).2.2.2
  have hgint := (intervalIntegrable_iff_integrableOn_Icc_of_le hv₀).mpr hg
  have hgnn : ENNReal.ofReal (∫ v in v₀..0, g v) = ∫⁻ v in Icc v₀ 0, ENNReal.ofReal (g v) := by
    rw [intervalIntegral.integral_of_le hv₀, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal hg hg0
  have hdreal : (∑ n, ∫ τ in s n..t n,
      ‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
        S.lam ((γ n).U τ) ((γ n).V τ) ^ 2) ≤ c⁻¹ * (∫ v in v₀..0, g v) := by
    have hnon n τ (_ : τ ∈ Icc (s n) (t n)) : 0 ≤
        ‖weightedJRepresentative e S ((γ n).U (s n)) ((γ n).U τ) ((γ n).V τ)‖ /
          S.lam ((γ n).U τ) ((γ n).V τ) ^ 2 := div_nonneg (norm_nonneg _) (sq_nonneg _)
    simp_rw [← ofReal_interval_integral (hst _) (hfi _).1 (hnon _)] at hd
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      intervalIntegral.integral_nonneg (hst n) (hnon n)), ← hgnn,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] at hd
    have hgpos : 0 ≤ ∫ v in v₀..0, g v := intervalIntegral.integral_nonneg_of_ae_restrict hv₀ hg0
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.mpr hc.le) hgpos)).mp hd
  have hepoint n τ (hτ : τ ∈ Icc (s n) (t n)) :
      ‖I * (e : ℂ) * S.Q ((γ n).U τ) ((γ n).V τ) * S.phi ((γ n).U τ) ((γ n).V τ) /
        (((1 - S.mu ((γ n).U τ) ((γ n).V τ)) * r n : ℝ) : ℂ)‖ ≤
          Ce * e ^ 2 * M₀ ^ 2 * F * r n := by
    let u := (γ n).U τ
    let v := (γ n).V τ
    have hu := (hcurve n τ hτ).1
    have hv := (hcurve n τ hτ).2
    have hpu := (γ n).mem τ hτ
    have huv := (hproper u hu).1
    rw [← hv] at huv
    have hcoreseg : outSeg u u v ⊆ origDomain ui := by
      rintro ⟨x, w⟩ ⟨rfl, hw⟩
      exact ⟨hpu.1, hpu.2.1, hw.1, hw.2.trans hpu.2.2.2⟩
    have hmass : S.m u v / S.r u v ≤ F ^ 2 := by
      rw [(γ n).radius τ hτ]
      have hh := hbudget n τ hτ
      linarith only [hh, (hE n).2, sq_nonneg ‖S.theta u v / S.lam u v‖]
    have hφ := hphi (u, v) (hp n τ hτ)
    have hy := (hstop _ (hp n τ hτ)).2.2.2.2.1
    have hqc := hcharge e M₀ F S (origDomain ui) u v v h.solution huv le_rfl hcoreseg
      hM hF hF1.le (fun w hw => hcore u hu w ⟨hw.1, hw.2.trans hpu.2.2.2⟩)
      (fun w hw => by have he : w = v := le_antisymm hw.2 hw.1; simpa only [he] using hφ)
      (fun w hw => by have he : w = v := le_antisymm hw.2 hw.1; simpa only [he] using hy) hmass
    have he := electric_forcing_of_profiles (E := F ^ 2) hδ hCq.le (by linarith only [hM] : 0 ≤ M₀)
      (h.solution.r_pos _ hpu huv) (hstop _ (hp n τ hτ)).2.1 hφ
      (by simpa only [Real.sqrt_sq hF] using hqc)
    simpa only [Real.sqrt_sq hF, (γ n).radius τ hτ] using he
  have hemint n : (∫ τ in s n..t n,
      ‖I * (e : ℂ) * S.Q ((γ n).U τ) ((γ n).V τ) * S.phi ((γ n).U τ) ((γ n).V τ) /
        (((1 - S.mu ((γ n).U τ) ((γ n).V τ)) * r n : ℝ) : ℂ)‖) ≤
      Ce * e ^ 2 * M₀ ^ 2 * F * (∫ τ in s n..t n, r n) := by
    have cQ := (γ n).continuousOn_trace h.solution.cont_Q
    have cφ := (γ n).continuousOn_trace h.solution.cont_phi
    have cμ := (Cylinder.continuousOn_normalized_traces h.solution (γ n)).2.2
    have cem : ContinuousOn (fun τ =>
        ‖I * (e : ℂ) * S.Q ((γ n).U τ) ((γ n).V τ) * S.phi ((γ n).U τ) ((γ n).V τ) /
          (((1 - S.mu ((γ n).U τ) ((γ n).V τ)) * r n : ℝ) : ℂ)‖) (Icc (s n) (t n)) :=
      (((continuousOn_const.mul (continuous_ofReal.comp_continuousOn cQ)).mul cφ).div
        (continuous_ofReal.comp_continuousOn ((continuousOn_const.sub cμ).mul_const (r n)))
        (fun τ hτ => Complex.ofReal_ne_zero.mpr (mul_ne_zero
          (h.solution.one_sub_mu_pos _ ((γ n).mem τ hτ)).ne' (hr n).ne'))).norm
    have hh := intervalIntegral.integral_mono_on (hst n)
      (cem.intervalIntegrable_of_Icc (μ := volume) (hst n))
      intervalIntegrable_const (hepoint n)
    rwa [intervalIntegral.integral_const_mul] at hh
  have helectric := Finset.sum_le_sum (fun n (_ : n ∈ Finset.univ) => hemint n)
  rw [← Finset.mul_sum] at helectric
  have helectric' := helectric.trans (mul_le_mul_of_nonneg_left
    (cylinder_radius_moment_sum h.solution hab hcont hstop hmem
      (fun u hu => (hproper u hu).1) N r s t γ hr hst hcurve hdisjU)
    (by dsimp only [Ce]; positivity))
  have htotal := Finset.sum_le_sum (fun n (_ : n ∈ Finset.univ) => (hfi n).2)
  simp only [Finset.sum_add_distrib] at htotal
  have hC₁ : Cn ≤ C := by
    have hh : 0 ≤ Ce * F / 2 := by dsimp only [Ce]; positivity
    dsimp only [C]; linarith only [hh]
  have hC₂ : Ce * F / 2 ≤ C := by dsimp only [C]; linarith only [hCn]
  have hsumE : 0 ≤ ∑ n, E n := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hzeta : 0 ≤ e ^ 2 * M₀ ^ 2 * S.r a 0 ^ 2 := by positivity
  calc
    _ ≤ _ := htotal
    _ ≤ c⁻¹ * (∫ v in v₀..0, g v) + Cn * (∑ n, E n) +
        Ce * e ^ 2 * M₀ ^ 2 * F * (S.r a 0 ^ 2 / 2) :=
      add_le_add (add_le_add hdreal hnb) helectric'
    _ = c⁻¹ * (∫ v in v₀..0, g v) + Cn * (∑ n, E n) +
        (Ce * F / 2) * (e ^ 2 * M₀ ^ 2 * S.r a 0 ^ 2) := by ring
    _ ≤ _ := add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hC₁ hsumE))
      (mul_le_mul_of_nonneg_right hC₂ hzeta)

end EmcsfAcExtension.Global
