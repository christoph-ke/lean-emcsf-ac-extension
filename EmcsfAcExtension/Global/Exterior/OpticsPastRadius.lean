module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Exterior.Main
import EmcsfAcExtension.Infra.Level.OrderIso
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Global.Exterior.OpticsPast
import EmcsfAcExtension.Global.Terminal.Hypotheses

/-! # Incoming radius derivatives and past invariance

Complete `charged_SF_new_version.tex:L1192–1195` and internal project record supporting optics with
the strict optical comparison and the actual radius-coordinate chain rule.
The inverse uses the original terminal radius on its open image.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

/-- [internal]
The terminal radius has one inverse on its entire open positive image.
Along every proper incoming ray, the radius expressed using this inverse
has derivative `ν/ν_top`. No optical estimate or inverse derivative is
assumed; both follow from the original characteristic equations and the
nonzero terminal expansion. There are no estimate constants. -/
theorem incoming_radius_coordinate (h : OriginalData ui e S) :
    ∃ U : ℝ → ℝ,
      (∀ u ∈ Ioo ui 0, U (S.r u 0) = u) ∧
      (∀ R ∈ Ioo 0 (S.r ui 0), S.r (U R) 0 = R) ∧
      ∀ u v, u ∈ Ioo ui 0 → u < v → v ≤ 0 →
        HasDerivAt (fun R => S.r (U R) v) (S.nu u v / S.nu u 0) (S.r u 0) := by
  let R := fun u => S.r u 0
  have hanti := (Terminal.terminal_radius_strictAntiOn h.solution).mono Ioo_subset_Ico_self
  have himage := Terminal.terminal_radius_image_Ioo h.ui_neg h.solution h.mu
  let E := Level.orderIsoOnAnti_of_image_eq hanti himage
  let U : ℝ → ℝ := fun r => if hr : r ∈ Ioo 0 (R ui) then
    ((E.symm ⟨r, hr⟩).ofDual : ℝ) else ui
  have hRmem (u : ℝ) (hu : u ∈ Ioo ui 0) : R u ∈ Ioo 0 (R ui) := by
    rw [← himage]
    exact mem_image_of_mem R hu
  have hU (u : ℝ) (hu : u ∈ Ioo ui 0) : U (R u) = u := by
    have he : E (OrderDual.toDual (⟨u, hu⟩ : Ioo ui 0)) = ⟨R u, hRmem u hu⟩ := by
      apply Subtype.ext
      exact Level.orderIsoOnAnti_of_image_eq_apply hanti himage _
    dsimp only [U]
    rw [dite_eq_left (hRmem u hu), ← he, E.symm_apply_apply]
    rfl
  have hRU (r : ℝ) (hr : r ∈ Ioo 0 (R ui)) : R (U r) = r := by
    have he := congrArg Subtype.val (E.apply_symm_apply ⟨r, hr⟩)
    simpa only [E, Level.orderIsoOnAnti_of_image_eq_apply, U, dite_eq_left hr] using he
  have cU : ContinuousOn U (Ioo 0 (R ui)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun r : Ioo 0 (R ui) => ((E.symm r).ofDual : ℝ)) :=
      continuous_subtype_val.comp E.symm.continuous
    apply hc.congr
    intro r
    dsimp only [U, Set.domRestrict]
    rw [dite_eq_left r.property]
  refine ⟨U, hU, hRU, ?_⟩
  intro u v hu huv hv
  have cn : ContinuousOn (fun s => S.nu s v) (Ioo ui v) :=
    h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs.1.le, hs.2.trans_le hv, hs.2.le, hv⟩)
  have hd : HasDerivAt (fun s => S.r s v) (S.nu u v) u := by
    apply Local.hasDerivAt_of_integralForm_interior ⟨hu.1, huv⟩ cn
    intro a b ha hab hb
    exact (h.solution.eq_in a b v hab hb
      ((inSeg_subset_origDomain_iff hab).2 ⟨ha.le, hb.trans_le hv, hb.le, hv⟩)).1
  have hdR := Terminal.terminal_radius_hasDerivAt h.solution hu
  have hi : HasDerivAt U (S.nu u 0)⁻¹ (R u) := by
    apply HasDerivAt.of_local_left_inverse
      ((cU _ (hRmem u hu)).continuousAt (isOpen_Ioo.mem_nhds (hRmem u hu)))
    · simpa only [hU u hu] using hdR
    · exact (h.solution.nu_neg (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩).ne
    · filter_upwards [isOpen_Ioo.mem_nhds (hRmem u hu)] with r hr
      exact hRU r hr
  simpa only [hU u hu, div_eq_mul_inv, Function.comp_def, R] using!
    (show HasDerivAt (fun s => S.r s v) (S.nu u v) (U (R u)) from by
      simpa only [hU u hu] using hd).comp (R u) hi

/-- [node c:exterior#incoming-past-invariance]
On one sufficiently late exterior, `ν/ν_top > 1/2 > k`, incoming pasts
remain exterior, and their separation from the frontier strictly grows
towards the past (`charged_SF_new_version.tex:L1192–1195`). The same terminal-radius
inverse gives `dr/dR = ν/ν_top` at every point of those pasts. The cutoff
depends on the fixed development, signed bound, admissible profile and
prescribed slope, uniformly in both labels. The inverse is constructed
from the original terminal radius, independently of the exterior cutoff. -/
theorem incoming_past_invariance_with_radius {k : ℝ}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∃ U : ℝ → ℝ,
      (∀ u ∈ Ioo ui 0, U (S.r u 0) = u) ∧
      (∀ R ∈ Ioo 0 (S.r ui 0), S.r (U R) 0 = R) ∧
      ∀ p ∈ adaptiveExterior S ui u₀ ell,
        (∀ s ∈ Icc u₀ p.1, (s, p.2) ∈ adaptiveExterior S ui u₀ ell) ∧
        StrictAntiOn (fun s => S.r s p.2 - ell (S.r s 0)) (Icc u₀ p.1) ∧
        ∀ s ∈ Icc u₀ p.1,
          1 / 2 < S.nu s p.2 / S.nu s 0 ∧ k < 1 / 2 ∧
          HasDerivAt (fun R => S.r (U R) p.2) (S.nu s p.2 / S.nu s 0) (S.r s 0) := by
  obtain ⟨up, hup, hpast⟩ := incoming_past_invariance h hs M ell hR hk hLip hmass
    hell hellsmall hsmall
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmassTail, hcollapse, htail,
    hlimit, hlog⟩ := (charged_terminal_equivalence ui e S h).2 hs
  obtain ⟨un, hun, hnu⟩ := uniform_nu_ratio_of_terminal h M ell hR hC hcollapse
    hmass hell hellsmall hsmall hlog (1 / 2) (by norm_num)
  obtain ⟨ur, hur, hrr⟩ := (show ∀ᶠ u in 𝓝[<] (0 : ℝ),
      u ∈ Ioo (max up un) 0 ∧ S.r u 0 < R₀ from by
    filter_upwards [Ioo_mem_nhdsLT (max_lt hup.2 hun.2),
      hcollapse.eventually (Iio_mem_nhds hR)] with u hu hr
    exact ⟨hu, hr⟩).exists
  have hpr : up ≤ ur := (le_max_left _ _).trans hur.1.le
  have hnr : un ≤ ur := (le_max_right _ _).trans hur.1.le
  have hui : ur ∈ Ioo ui 0 := ⟨hup.1.trans_le hpr, hur.2⟩
  obtain ⟨U, hU, hRU, hd⟩ := incoming_radius_coordinate h
  refine ⟨ur, hui, U, hU, hRU, ?_⟩
  intro p hp
  obtain ⟨hkeep, hsep⟩ := hpast p ⟨hp.1, hpr.trans hp.2.1, hp.2.2⟩
  have hkeep' (s : ℝ) (hs : s ∈ Icc ur p.1) :
      (s, p.2) ∈ adaptiveExterior S ui ur ell :=
    ⟨(hkeep s ⟨hpr.trans hs.1, hs.2⟩).1, hs.1,
      (hkeep s ⟨hpr.trans hs.1, hs.2⟩).2.2⟩
  refine ⟨hkeep', hsep.mono (Icc_subset_Icc hpr le_rfl), ?_⟩
  intro s hs'
  have hsp := hkeep' s hs'
  have hsu : s ∈ Ioo ui 0 := ⟨hui.1.trans_le hs'.1, hs'.2.trans_lt hp.1.2.1⟩
  have hs0 : (s, 0) ∈ origDomain ui := ⟨hsu.1.le, hsu.2, hsu.2.le, le_rfl⟩
  have hsr : S.r s 0 ∈ Ioc 0 R₀ :=
    ⟨h.solution.r_pos _ hs0 hsu.2,
      ((Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
        ⟨hui.1.le, hui.2⟩ ⟨hsu.1.le, hsu.2⟩ hs'.1).trans hrr.le⟩
  have hproper : s < p.2 := by
    by_contra hn
    have heq : p.2 = s := le_antisymm (le_of_not_gt hn) hsp.1.2.2.1
    have hz := (h.solution.axis s ⟨hsu.1.le, hsu.2, le_rfl, hsu.2.le⟩).1
    have hr := (hell _ hsr).trans_le hsp.2.2
    rw [heq, hz] at hr
    exact (lt_irrefl 0) hr
  have hn := hnu (s, p.2) ⟨hsp.1, hnr.trans hs'.1, hsp.2.2⟩
  refine ⟨?_, by linarith only [hk.2], hd s p.2 hsu hproper hp.1.2.2.2⟩
  have hl := (abs_lt.mp hn).1
  linarith only [hl]

end EmcsfAcExtension.Global.Exterior
