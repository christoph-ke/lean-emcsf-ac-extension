module

public import EmcsfAcExtension.Local.Construction.FullSystemCarrier
import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
import EmcsfAcExtension.Local.Construction.FullSystemRegularity
import EmcsfAcExtension.Local.Construction.FullSystem
import EmcsfAcExtension.Local.Construction.ReconBasic
import EmcsfAcExtension.Local.Calculus.MixedIdentity
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Complete C¹ recovery on the original closed wedge

internal project record (19)–(20), L377–L398. The mixed jets come from
incoming primitives. Sectional FTC extends them to every endpoint,
including the axis and collapsed corner sections. No C² premise is used.
-/

public section

open Set Complex MeasureTheory

namespace EmcsfAcExtension.Local.Null

/-- A C¹ incoming transport source supplies the continuous incoming
jet of the outgoing partial on the whole closed wedge. The primitive
argument is first applied on off-axis rectangles, then sectional FTC
includes both endpoints and the axis. There are no estimate constants. -/
theorem mixed_u_pdV_on_wedge_of_transport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} {f F : ℝ → ℝ → E} (hac : a < c) (hcb : c ≤ b)
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cF : ContDiffOn ℝ 1 (Function.uncurry F)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hF : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f p.1 p.2 = F p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    ContinuousOn (Function.uncurry (pdV D F)) D ∧
      ∀ p ∈ D, HasDerivWithinAt (fun x => pdV D f x p.2)
        (pdV D F p.1 p.2) (Icc a (min c p.2)) p.1 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  have hD := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have cJ := continuousOn_pdV cF hD
  refine ⟨cJ, ?_⟩
  intro p hp
  have hs : MapsTo (fun x => (x, p.2)) (Icc a (min c p.2)) D :=
    fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩,
      (le_min_iff.mp hx.2).1⟩
  have cj := cJ.comp (continuousOn_id.prodMk continuousOn_const) hs
  have cp := (continuousOn_pdV cf hD).comp
    (continuousOn_id.prodMk continuousOn_const) hs
  have hd (x : ℝ) (hx : x ∈ Ioo a (min c p.2)) :
      HasDerivAt (fun t => pdV D f t p.2) (pdV D F x p.2) x := by
    let v₀ := (x + p.2) / 2
    let U := min c v₀
    have hxv : x < p.2 := hx.2.trans_le (min_le_right _ _)
    have hxv₀ : x < v₀ := by dsimp [v₀]; linarith only [hxv]
    have hv₀v : v₀ < p.2 := by dsimp [v₀]; linarith only [hxv]
    have hxU : x < U := lt_min (hx.2.trans_le (min_le_left _ _)) hxv₀
    have hrect : Icc a U ×ˢ Icc v₀ b ⊆ D := by
      intro q hq
      exact ⟨⟨hq.1.1, (hq.1.2.trans (min_le_right _ _)).trans hq.2.1, hq.2.2⟩,
        hq.1.2.trans (min_le_left _ _)⟩
    have hswap : MapsTo (fun q : ℝ × ℝ => (q.2, q.1))
        (Icc v₀ b ×ˢ Icc a U) D := fun q hq => hrect ⟨hq.2, hq.1⟩
    exact (mixed_u_pdV_of_transport_aux (f := f) (G := F) (Gv := pdV D F) (hx.1.trans hxU)
      (hv₀v.trans_le hp.1.2.2) hrect cf
      (cF.continuousOn.comp (continuousOn_snd.prodMk continuousOn_fst) hswap)
      (cJ.comp (continuousOn_snd.prodMk continuousOn_fst) hswap)
      (fun t ht y hy => hF (t, y) (hrect ⟨ht, hy⟩))
      (fun y hy t ht => hasDerivWithinAt_pdV cF (hrect ⟨ht, hy⟩)
        (fun z hz => hrect ⟨ht, hz⟩))
      ⟨hx.1.le, hxU.le⟩ ⟨hv₀v.le, hp.1.2.2⟩).hasDerivAt (Icc_mem_nhds hx.1 hxU)
  have hrep (x : ℝ) (hx : x ∈ Icc a (min c p.2)) :
      pdV D f x p.2 = pdV D f a p.2 + ∫ t in a..x, pdV D F t p.2 := by
    have hsub : Icc a x ⊆ Icc a (min c p.2) := Icc_subset_Icc le_rfl hx.2
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (cp.mono hsub) (fun t ht => hd t ⟨ht.1, ht.2.trans_le hx.2⟩)
      ((cj.mono hsub).intervalIntegrable_of_Icc hx.1)
    change (∫ t in a..x, pdV D F t p.2) = pdV D f x p.2 - pdV D f a p.2 at he
    rw [he]
    abel
  have hpoint : p.1 ∈ Icc a (min c p.2) := ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩
  have h := (hasDerivWithinAt_const p.1 (Icc a (min c p.2)) (pdV D f a p.2)).add
    (Recon.hasDerivWithinAt_primitive cj hpoint)
  simp only [zero_add] at h
  exact h.congr (fun x hx => hrep x hx) (hrep p.1 hpoint)

/-- [node restart-sec-independent-null-construction#c1-regularity]
Complete internal project record (19)–(20) from the raw internal project record carrier:
the pair and all nine primary fields are C¹, both incoming transport
equations hold, and both outgoing jets have continuous incoming
within derivatives on every original closed section. The fixed bounds
`l,κ` precede the candidate; there are no estimate constants. -/
theorem c1_regularity
    {a b c l κ e : ℝ} {lam lamV : ℝ → ℝ → ℝ} {hh hhV : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hac : a < c) (hcb : c ≤ b)
    (hl : 0 < l) (hκ : 0 < κ)
    (_cLam₀ : ContDiffOn ℝ 1 lam₀ (Icc a b))
    (_cH₀ : ContDiffOn ℝ 1 h₀ (Icc a b))
    (cl : ContinuousOn (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContinuousOn (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (clV : ContinuousOn (Function.uncurry lamV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (chV : ContinuousOn (Function.uncurry hhV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (fl : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      lam p.1 p.2 = lam p.1 p.1 + ∫ s in p.1..p.2, lamV p.1 s)
    (fh : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      hh p.1 p.2 = hh p.1 p.1 + ∫ s in p.1..p.2, hhV p.1 s)
    (cG : ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContinuousOn (Function.uncurry (Recon.A e lam hh))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cP : ContinuousOn (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2)
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
    let S := Recon.toFields e lam hh
    let G := fun u v => Recon.nu e lam hh u v / Recon.r lam u v * Recon.z e lam hh u v
    let P := fun u v =>
      (((-Recon.nu e lam hh u v / Recon.r lam u v : ℝ) : ℂ) *
        ((Recon.z e lam hh u v : ℂ) * Recon.ratio lam hh u v +
          I * e * Recon.Q e lam hh u v * Recon.phi lam hh u v /
            (1 - (Recon.mu e lam hh u v : ℂ))))
    let FL := fun u v => lam u v * G u v
    let FH := fun u v => -(I * e * S.A u v) * hh u v + P u v
    (ContDiffOn ℝ 1 (Function.uncurry hh) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.r) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.lam) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.nu) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.m) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.Q) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.phi) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.A) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.theta) D ∧
      ContDiffOn ℝ 1 (Function.uncurry S.xi) D) ∧
      (∀ p ∈ D, pdU D lam p.1 p.2 = FL p.1 p.2 ∧
        pdU D hh p.1 p.2 = FH p.1 p.2) ∧
      ContinuousOn (Function.uncurry (pdV D FL)) D ∧
      ContinuousOn (Function.uncurry (pdV D FH)) D ∧
      ∀ p ∈ D,
        HasDerivWithinAt (fun x => pdV D lam x p.2) (pdV D FL p.1 p.2)
          (Icc a (min c p.2)) p.1 ∧
        HasDerivWithinAt (fun x => pdV D hh x p.2) (pdV D FH p.1 p.2)
          (Icc a (min c p.2)) p.1 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let G := fun u v => Recon.nu e lam hh u v / Recon.r lam u v * Recon.z e lam hh u v
  let P := fun u v =>
    (((-Recon.nu e lam hh u v / Recon.r lam u v : ℝ) : ℂ) *
      ((Recon.z e lam hh u v : ℂ) * Recon.ratio lam hh u v +
        I * e * Recon.Q e lam hh u v * Recon.phi lam hh u v /
          (1 - (Recon.mu e lam hh u v : ℂ))))
  let FL := fun u v => lam u v * G u v
  let FH := fun u v => -(I * e * Recon.A e lam hh u v) * hh u v + P u v
  obtain ⟨cl1, ch1⟩ := contDiffOn_pair_of_picard_carrier hac hcb cl ch clV chV fl fh cG cA cP hL hH
  obtain ⟨_, _, _, _, _, cA1, cG1, cP1⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl1 ch1 hlo hgap
  have cFL : ContDiffOn ℝ 1 (Function.uncurry FL) D := cl1.mul cG1
  have cFH : ContDiffOn ℝ 1 (Function.uncurry FH) D :=
    (((contDiffOn_const (c := I * e)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cA1)).neg.mul ch1).add cP1
  have hFL := pdU_lam_on_wedge_of_picard hac hcb cl1 cG hL
  have hFH : ∀ p ∈ D, pdU D hh p.1 p.2 = FH p.1 p.2 := by
    apply pdU_on_wedge_eq_of_sectional hac hcb ch1 cFH.continuousOn
    intro p hp
    have hs : MapsTo (fun x => (x, p.2)) (Icc a (min c p.2)) D :=
      fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩, (le_min_iff.mp hx.2).1⟩
    exact Recon.hasDerivWithinAt_h_of_picardH
      (cA.comp (f := fun x : ℝ => (x, p.2))
        (continuousOn_id.prodMk continuousOn_const) hs)
      (cP.comp (f := fun x : ℝ => (x, p.2))
        (continuousOn_id.prodMk continuousOn_const) hs)
      ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩ (fun x hx => hH (x, p.2) (hs hx))
  obtain ⟨cJL, hJL⟩ := mixed_u_pdV_on_wedge_of_transport hac hcb cl1 cFL hFL
  obtain ⟨cJH, hJH⟩ := mixed_u_pdV_on_wedge_of_transport hac hcb ch1 cFH hFH
  exact ⟨smooth_regularity_of_picard hac hcb hl hκ cl1 ch1 hlo hgap hL hH,
    fun p hp => ⟨hFL p hp, hFH p hp⟩, cJL, cJH, fun p hp => ⟨hJL p hp, hJH p hp⟩⟩

end EmcsfAcExtension.Local.Null
