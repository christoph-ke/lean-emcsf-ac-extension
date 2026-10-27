module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.Corner
import EmcsfAcExtension.Local.Construction.ContinuationParameters2
import EmcsfAcExtension.Local.Construction.CornerAssembly
import EmcsfAcExtension.Local.Construction.StripAssembly
import EmcsfAcExtension.Local.Construction.WholeGeometry
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Reaching the closed terminal triangle

The order-theoretic argument is separated from construction of the strip.
Its extension premise includes the cap at `T`; equality of a supremum with
`T` alone is never used to assert existence at the terminal apex.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Abstract maximal-apex argument with an actual capped final extension.
The extension radius is uniform for apex coordinates near each candidate
supremum and may depend on that supremum and the fixed problem.
The conclusion includes the endpoint; no closedness premise is needed. -/
theorem terminal_membership_of_uniform_capped_extension {T : ℝ} {P : ℝ → Prop}
    (hstart : ∃ s : ℝ, 0 < s ∧ s ≤ T ∧ P s)
    (hmono : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ T → P t → P s)
    (hextend : ∀ q : ℝ, 0 < q → q ≤ T →
      (∀ s : ℝ, 0 < s → s < q → P s) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < q → q - δ < s →
        P s → P (min T (s + δ))) : P T := by
  let A : Set ℝ := {s | 0 < s ∧ s ≤ T ∧ P s}
  obtain ⟨s₀, hs₀, hs₀T, hP₀⟩ := hstart
  have hne : A.Nonempty := ⟨s₀, hs₀, hs₀T, hP₀⟩
  have hbd : BddAbove A := ⟨T, fun _ hs => hs.2.1⟩
  let q := sSup A
  have hq : 0 < q := hs₀.trans_le (le_csSup hbd (show s₀ ∈ A from ⟨hs₀, hs₀T, hP₀⟩))
  have hqT : q ≤ T := csSup_le hne (fun _ hs => hs.2.1)
  have hbelow : ∀ s : ℝ, 0 < s → s < q → P s := by
    intro s hs hsq
    obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup hne hsq
    exact hmono s t hs hst.le ht.2.1 ht.2.2
  obtain ⟨δ, hδ, hstep⟩ := hextend q hq hqT hbelow
  let s := max (q / 2) (q - δ / 2)
  have hs : 0 < s := (by linarith : (0 : ℝ) < q / 2).trans_le (le_max_left _ _)
  have hsq : s < q := max_lt (by linarith) (by linarith)
  have hclose : q - δ < s := by
    have h := le_max_right (q / 2) (q - δ / 2)
    dsimp only [s]
    linarith
  have hcap := hstep s hs hsq hclose (hbelow s hs hsq)
  have hqsδ : q < s + δ := by linarith
  have hqeq : q = T := by
    apply le_antisymm hqT
    by_contra hnot
    have hqT' : q < T := lt_of_not_ge hnot
    have hqcap : q < min T (s + δ) := lt_min hqT' hqsδ
    have hmem : min T (s + δ) ∈ A :=
      ⟨hq.trans hqcap, min_le_left _ _, hcap⟩
    exact (not_lt_of_ge (le_csSup hbd hmem)) hqcap
  have hTcap : min T (s + δ) = T := min_eq_left (by simpa only [hqeq] using hqsδ.le)
  simpa only [hTcap] using hcap

/-- Downward closure of classical complete-triangle existence with the
fixed restart datum. Unique differentiation is used only on positive
smaller triangles, in accordance with internal project record. -/
theorem c1_triangle_existence_mono {e s t : ℝ} {h : ℝ → ℂ}
    (hs : 0 < s) (hst : s ≤ t)
    (hex : ∃ F : Fields, IsC1Solution e F (triangle 0 t) ∧ IsRestartData F h t) :
    ∃ F : Fields, IsC1Solution e F (triangle 0 s) ∧ IsRestartData F h s := by
  obtain ⟨F, hF, hdata⟩ := hex
  exact ⟨F, hF.mono (triangle_subset_triangle hst) (uniqueDiffOn_triangle hs),
    isRestartData_mono hdata hst⟩

/-- Complete closed-triangle existence from a positive initial triangle
and a uniform capped extension near each candidate maximal apex.
This helper records the exact remaining construction obligation; the
extension premise is not an allowed substitute for the strip proof. -/
theorem whole_triangle_solution_of_capped_extension {T e : ℝ} {h : ℝ → ℂ}
    (hstart : ∃ (s : ℝ) (F : Fields), 0 < s ∧ s ≤ T ∧
      IsC1Solution e F (triangle 0 s) ∧ IsRestartData F h s)
    (hextend : ∀ q : ℝ, 0 < q → q ≤ T →
      (∀ s : ℝ, 0 < s → s < q →
        ∃ F : Fields, IsC1Solution e F (triangle 0 s) ∧ IsRestartData F h s) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < q → q - δ < s →
        (∃ F : Fields, IsC1Solution e F (triangle 0 s) ∧ IsRestartData F h s) →
        ∃ F : Fields, IsC1Solution e F (triangle 0 (min T (s + δ))) ∧
          IsRestartData F h (min T (s + δ))) :
    ∃ F : Fields, IsC1Solution e F (triangle 0 T) ∧ IsRestartData F h T := by
  apply terminal_membership_of_uniform_capped_extension (T := T)
  · obtain ⟨s, F, hs, hsT, hF, hdata⟩ := hstart
    exact ⟨s, hs, hsT, F, hF, hdata⟩
  · intro s t hs hst _ht
    exact c1_triangle_existence_mono hs hst
  · exact hextend


/-- [internal]
In the C¹ reading of charged_SF_new_version.tex:L6291–6315, every admissible C¹ datum
has a full closed-triangle solution. The universal smallness thresholds
precede `T,e,h`. The common first-jet bound fixes the enlarged cone class
and its short-cone time before the corner width; the actual strip then
fixes a positive height uniform in the old apex. The capped extension
includes the terminal edge and apex even when the maximal apex is `T`.
Only the four approved producer inputs are used. -/
theorem whole_triangle_solution_of_inputs
    (hOriginal : ContinuationOriginalPicardInput) (hShort : ContinuationShortPicardInput)
    (hRecovery : ContinuationRecoveryInput) (hBound : ContinuationC1BoundInput) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ F : Fields, IsC1Solution e F (triangle 0 T) ∧ IsRestartData F h T := by
  obtain ⟨ε,δ,hε,hδ,hparams⟩ :=
    enlarged_continuation_parameters_of_inputs hOriginal hShort hRecovery hBound
  refine ⟨ε,δ,hε,hδ,?_⟩
  intro T e h hT hh hsmall hscale
  obtain ⟨a,F₀,J,yi,B_AP,Ci,B,Bc,ℓ,τ,ha,haT,hF₀,hdata₀,
    _hJ,hLip,hYiC,hYiEq,hB_AP,hCi,hBdef,hBpos,_hJB,_hCiB,
    _hTrace,_hTraceB,hcommon,hℓdef,hℓ,_hBc,_hBcdef,_hτ,_hshort,_hηparams⟩ :=
    hparams T e h hT hh hsmall hscale
  have hBquarter : 1 ≤ B/4 := by
    rw [hBdef]
    have hJnonneg := J.coe_nonneg
    linarith only [hB_AP,hCi,hJnonneg]
  have hB : 1 ≤ B := by linarith only [hBquarter]
  have hℓB : ℓ ≤ (B/4)⁻¹ := by
    rw [hℓdef]
    exact inv_anti₀ (by linarith only [hBquarter]) (by linarith only [hBpos])
  obtain ⟨τcorner,hτcorner,hcorner⟩ :=
    c1_axis_corner_fill_of_inputs hShort hRecovery B ℓ e hB hℓ
  apply whole_triangle_solution_of_capped_extension
  · exact ⟨a,F₀,ha,haT,
      hF₀.mono (triangle_subset_continuationWedge haT) (uniqueDiffOn_triangle ha),
      isRestartData_mono hdata₀ haT⟩
  · intro q hq hqT _hbelow
    obtain ⟨η,hη,_hηq,_hητ,hband⟩ := continuation_capped_band_geometry hq hτcorner
    obtain ⟨δstrip,hδstrip,hstrip⟩ := c1_positive_radius_strip
      (B/4) ℓ η J yi hT hBquarter hℓ hη hℓB hLip hYiC
      ha haT hF₀ hdata₀ hYiEq
    obtain ⟨Δ,hΔ,_hΔstrip,_hΔη,_hΔτ,hgeometry⟩ := hband δstrip hδstrip
    refine ⟨Δ,hΔ,?_⟩
    intro S hS hSq hclose hex
    obtain ⟨_hhalf,hηS,hc,hcd,hdS,hSb,hbT,hheight,hlength⟩ :=
      hgeometry T S hqT hclose hSq
    obtain ⟨Old,hOld,hdataOld⟩ := hex
    have hsT : S ≤ T := hSq.le.trans hqT
    have hOldBound := (hcommon S Old hS hsT hOld hdataOld).2
    obtain ⟨H,hH,_hHO,hreal,hcomplex,hmargin,hdataH,hgaugeH,_hfullstate⟩ :=
      hstrip S (min T (S+Δ)) hηS hSb hheight hbT Old hOld hdataOld hOldBound
    have hfour : 4*(B/4) = B := by ring
    rw [hfour] at hreal hcomplex
    obtain ⟨F,hF,hdataF,_hFH⟩ :=
      hcorner (S-η) (S-3*η/4) S (min T (S+Δ)) H h
        hc hcd hdS hSb hlength hH hreal hcomplex hmargin hdataH hgaugeH
    exact ⟨F,hF,hdataF⟩

end EmcsfAcExtension.Local
