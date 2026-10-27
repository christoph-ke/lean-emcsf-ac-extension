module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Minima on proper apex triangles

The continuous projection onto a complete triangle reduces changing-domain
minima to minima over a fixed compact set. Positivity is used only for the
positive-minimum conclusion (internal project record, binding F01).
Source: charged_SF_new_version.tex:L1802–1808.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.LateGap

/-- [internal] The literal minimum-value expression on an apex triangle.
Its attainment and continuity below require a continuous function and ordered
endpoints; no minimizer or data-dependent constant is chosen. -/
noncomputable def apexMinimum (g : ℝ × ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (g '' triangle a b)

/-- [internal] A continuous function attains its apex minimum, without a sign
assumption, including on the initial singleton triangle. -/
theorem apexMinimum_attained {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (triangle a b)) :
    ∃ p ∈ triangle a b, apexMinimum g a b = g p ∧
      ∀ q ∈ triangle a b, g p ≤ g q :=
  (isCompact_triangle a b).exists_sInf_image_eq_and_le
    ⟨(a, a), le_rfl, le_rfl, hab⟩ hg

/-- [internal] Every value on a complete triangle bounds its minimum above. -/
theorem apexMinimum_le {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (triangle a b)) {p : ℝ × ℝ} (hp : p ∈ triangle a b) :
    apexMinimum g a b ≤ g p := by
  obtain ⟨q, _, hq, hmin⟩ := apexMinimum_attained (hp.1.trans (hp.2.1.trans hp.2.2)) hg
  rw [hq]
  exact hmin p hp

/-- [internal] A lower bound for all triangle values bounds the minimum. -/
theorem le_apexMinimum {g : ℝ × ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (triangle a b))
    (hc : ∀ p ∈ triangle a b, c ≤ g p) : c ≤ apexMinimum g a b := by
  obtain ⟨p, hp, he, _⟩ := apexMinimum_attained hab hg
  rw [he]
  exact hc p hp

/-- [internal] Positivity is needed here, and is not a premise of the
continuity or attainment lemmas. -/
theorem apexMinimum_pos {g : ℝ × ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (triangle a b))
    (hpos : ∀ p ∈ triangle a b, 0 < g p) : 0 < apexMinimum g a b := by
  obtain ⟨p, hp, he, _⟩ := apexMinimum_attained hab hg
  rw [he]
  exact hpos p hp

/-- [internal] The initial triangle is a singleton. -/
theorem apexMinimum_self (g : ℝ × ℝ → ℝ) (a : ℝ) :
    apexMinimum g a a = g (a, a) := by
  have he : triangle a a = {(a, a)} := by
    ext p
    constructor
    · intro hp
      have hu := le_antisymm (hp.2.1.trans hp.2.2) hp.1
      have hv := le_antisymm hp.2.2 (hp.1.trans hp.2.1)
      exact Prod.ext hu hv
    · rintro rfl
      exact ⟨le_rfl, le_rfl, le_rfl⟩
  simp [apexMinimum, he]

/-- [internal] Apex minima are antitone under triangle inclusion. -/
theorem apexMinimum_antitoneOn {g : ℝ × ℝ → ℝ} {a B : ℝ}
    (hg : ContinuousOn g (triangle a B)) :
    AntitoneOn (apexMinimum g a) (Icc a B) := by
  intro b hb c hc hbc
  have hsub : triangle a b ⊆ triangle a c := fun _ hp =>
    ⟨hp.1, hp.2.1, hp.2.2.trans hbc⟩
  obtain ⟨p, hp, he, _⟩ := apexMinimum_attained hb.1
    (hg.mono (fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.trans hb.2⟩))
  rw [he]
  exact apexMinimum_le (hg.mono (fun _ hp => ⟨hp.1, hp.2.1, hp.2.2.trans hc.2⟩))
    (hsub hp)

/-- [internal] Continuity of minima on a compact interval of apex labels.
There is no positivity assumption, and `a = B` is permitted. -/
theorem continuousOn_apexMinimum {g : ℝ × ℝ → ℝ} {a B : ℝ}
    (haB : a ≤ B) (hg : ContinuousOn g (triangle a B)) :
    ContinuousOn (apexMinimum g a) (Icc a B) := by
  let G : ℝ × ℝ → ℝ := fun p => g (triangleProj a B p)
  have cG : Continuous G := hg.comp_continuous (continuous_triangleProj a B)
    (triangleProj_mem haB)
  let F : ℝ → ℝ × ℝ → ℝ := fun b p => G (triangleProj a b p)
  have cF : Continuous (Function.uncurry F) := by
    apply cG.comp
    dsimp [triangleProj]
    fun_prop
  have cc : Continuous (fun b : ℝ => sInf (F b '' triangle a B)) :=
    (isCompact_triangle a B).continuous_sInf (f := F) cF
  apply cc.continuousOn.congr
  intro b hb
  symm
  change sInf (F b '' triangle a B) = sInf (g '' triangle a b)
  congr 1
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hq := triangleProj_mem hb.1 p
    refine ⟨triangleProj a b p, hq, ?_⟩
    dsimp [F, G]
    rw [triangleProj_of_mem (show triangleProj a b p ∈ triangle a B from
      ⟨hq.1, hq.2.1, hq.2.2.trans hb.2⟩)]
  · rintro ⟨p, hp, rfl⟩
    have hpB : p ∈ triangle a B := ⟨hp.1, hp.2.1, hp.2.2.trans hb.2⟩
    exact ⟨p, hpB, by simp only [F, G, triangleProj_of_mem hp, triangleProj_of_mem hpB]⟩

/-- [internal]
On every proper compact apex interval the gap minimum is continuous,
antitone, attained, strictly positive, and initially one. There is no claim
at the missing vertex. No terminal or smallness premise is used. -/
theorem apex_minimum_compact_interval {ui e a B : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hia : ui ≤ a)
    (haB : a ≤ B) (hB : B < 0) :
    let g := fun p : ℝ × ℝ => 1 - S.mu p.1 p.2
    ContinuousOn (apexMinimum g a) (Icc a B) ∧
      AntitoneOn (apexMinimum g a) (Icc a B) ∧
      apexMinimum g a a = 1 ∧
      ∀ b ∈ Icc a B, 0 < apexMinimum g a b ∧
        ∃ p ∈ triangle a b, apexMinimum g a b = g p := by
  dsimp only
  have hs := triangle_subset_origDomain hia hB
  have cg := ((continuousOn_const (c := (1 : ℝ))).sub (Gap.continuousOn_mu hS)).mono hs
  refine ⟨continuousOn_apexMinimum haB cg, apexMinimum_antitoneOn cg, ?_, ?_⟩
  · rw [apexMinimum_self]
    have hp := hs (show (a, a) ∈ triangle a B from ⟨le_rfl, le_rfl, haB⟩)
    simp [Fields.mu, (hS.axis a hp).1]
  · intro b hb
    have hsb : triangle a b ⊆ origDomain ui := triangle_subset_origDomain hia (hb.2.trans_lt hB)
    have cb := ((continuousOn_const (c := (1 : ℝ))).sub (Gap.continuousOn_mu hS)).mono hsb
    obtain ⟨p, hp, he, _⟩ := apexMinimum_attained hb.1 cb
    exact ⟨apexMinimum_pos hb.1 cb (fun p hp => hS.one_sub_mu_pos p (hsb hp)), p, hp, he⟩

/-- [node prop:charged-late-gap#apex-minimum-continuity]
The gap minimum is continuous and antitone on the entire half-open interval
of proper apex labels, is attained and positive at every such label, and
starts at one. No minimum or continuity at the missing endpoint is asserted.
This uses no terminal bound, optical bound, or scalar smallness. -/
theorem apex_minimum_continuity {ui e a : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hia : ui ≤ a) (ha : a < 0) :
    let g := fun p : ℝ × ℝ => 1 - S.mu p.1 p.2
    ContinuousOn (apexMinimum g a) (Ico a 0) ∧
      AntitoneOn (apexMinimum g a) (Ico a 0) ∧
      apexMinimum g a a = 1 ∧
      ∀ b ∈ Ico a 0, 0 < apexMinimum g a b ∧
        ∃ p ∈ triangle a b, apexMinimum g a b = g p := by
  dsimp only
  refine ⟨?_, ?_, (apex_minimum_compact_interval hS hia le_rfl ha).2.2.1, ?_⟩
  · intro b hb
    obtain ⟨B, hbB, hB⟩ := exists_between hb.2
    have hc := (apex_minimum_compact_interval hS hia (hb.1.trans hbB.le) hB).1
      b ⟨hb.1, hbB.le⟩
    apply hc.mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hbB)] with c hc hcB
    exact ⟨hc.1, hcB.le⟩
  · intro b hb c hc hbc
    exact (apex_minimum_compact_interval hS hia hc.1 hc.2).2.1
      ⟨hb.1, hbc⟩ ⟨hc.1, le_rfl⟩ hbc
  · intro b hb
    exact (apex_minimum_compact_interval hS hia hb.1 hb.2).2.2.2 b ⟨hb.1, le_rfl⟩

end EmcsfAcExtension.Global.LateGap
