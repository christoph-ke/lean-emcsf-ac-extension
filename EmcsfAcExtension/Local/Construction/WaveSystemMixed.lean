module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Local.Construction.FullSystemMixed
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.DiagonalChain
import EmcsfAcExtension.Local.Construction.Defects

/-! # Mixed partials and recovery of the incoming radius derivative

The smooth calculus step in internal project record `#first-order-wave-system`,
`charged_SF_new_version.tex:L6141–6146`. All derivatives are within the construction
triangle, including at its edges and corners.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Null

/-- The diagonal chain rule on the full closed construction wedge. The
trace interval is `[a,c]`, including its endpoints. -/
theorem hasDerivWithinAt_diagonal_wedge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c t : ℝ} {f : ℝ → ℝ → E}
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hcb : c ≤ b) (ht : t ∈ Icc a c) :
    HasDerivWithinAt (fun x => f x x)
      (pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f t t +
        pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f t t) (Icc a c) t := by
  have hp : (t, t) ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c} :=
    ⟨⟨ht.1, le_rfl, ht.2.trans hcb⟩, ht.2⟩
  have hd := ((cf.differentiableOn (by norm_num) (t, t) hp).hasFDerivWithinAt).comp_hasDerivWithinAt
    (f := fun x : ℝ => (x, x)) (s := Icc a c) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_id t)).hasDerivWithinAt)
    (fun x hx => ⟨⟨hx.1, le_rfl, hx.2.trans hcb⟩, hx.2⟩)
  convert hd using 1
  · funext x; rfl
  · change _ = fderivWithin ℝ (Function.uncurry f) _ (t, t) (1, 1)
    rw [show ((1, 1) : ℝ × ℝ) = (1, 0) + (0, 1) by ext <;> simp, map_add]
    rfl

/-- [node restart-sec-independent-null-construction#radius-null-identity]
Recover the incoming radius equation on the entire closed construction
wedge by differentiating its outgoing primitive, internal project record (21)–(22).
The radius is only C¹; the C¹ outgoing source supplies the particular mixed
derivative needed by FTC. Neither `r_u = ν` nor C² regularity is assumed.
There are no estimate constants. -/
theorem radius_null_identity_on_wedge_of_outgoing_and_transport {a b c : ℝ}
    {r lam nu : ℝ → ℝ → ℝ} (hac : a < c) (hcb : c ≤ b)
    (cr : ContDiffOn ℝ 1 (Function.uncurry r)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cn : ContDiffOn ℝ 1 (Function.uncurry nu)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hrv : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) r p.1 p.2 = lam p.1 p.2)
    (hln : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) lam p.1 p.2 =
        pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) nu p.1 p.2)
    (hr0 : ∀ t ∈ Icc a c, r t t = 0)
    (hn0 : ∀ t ∈ Icc a c, nu t t = -lam t t) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) r p.1 p.2 = nu p.1 p.2 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  have hD : UniqueDiffOn ℝ D := uniqueDiffOn_triangle_inter_fst_le hac hcb
  have cU := continuousOn_pdU cr hD
  have haxis (t : ℝ) (ht : t ∈ Icc a c) : pdU D r t t - nu t t = 0 := by
    have hd := hasDerivWithinAt_diagonal_wedge cr hcb ht
    have hz : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
        (pdU D r t t + pdV D r t t) (Icc a c) t :=
      hd.congr (fun s hs => (hr0 s hs).symm) (hr0 t ht).symm
    have heq := hz.derivWithin (uniqueDiffOn_Icc hac t ht)
    rw [(hasDerivWithinAt_const t (Icc a c) (0 : ℝ)).derivWithin
      (uniqueDiffOn_Icc hac t ht)] at heq
    rw [hrv (t, t) ⟨⟨ht.1, le_rfl, ht.2.trans hcb⟩, ht.2⟩] at heq
    rw [hn0 t ht]
    linarith only [heq]
  intro p hp
  have hu : p.1 ∈ Icc a c := ⟨hp.1.1, hp.2⟩
  have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b) D :=
    fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
  have cf : ContinuousOn (fun v => pdU D r p.1 v - nu p.1 v) (Icc p.1 b) :=
    (cU.sub cn.continuousOn).comp (continuousOn_const.prodMk continuousOn_id) hs
  have heq := eq_zero_of_homogeneous_transport (hu.2.trans hcb) cf
    (continuousOn_const (c := (0 : ℝ))) (haxis p.1 hu) (fun v hv => by
      have hd := (hasDerivAt_pdU_of_pdV_on_wedge hac hcb cr cl hrv hu hv.1 hv.2).sub
        ((hasDerivWithinAt_pdV cn (hs ⟨hv.1.le, hv.2.le⟩) hs).hasDerivAt
          (Icc_mem_nhds hv.1 hv.2))
      rw [hln (p.1, v) (hs ⟨hv.1.le, hv.2.le⟩), sub_self] at hd
      simpa only [zero_mul, Pi.sub_apply] using! hd) p.2 ⟨hp.1.2.1, hp.1.2.2⟩
  exact sub_eq_zero.mp heq

end EmcsfAcExtension.Local.Null
