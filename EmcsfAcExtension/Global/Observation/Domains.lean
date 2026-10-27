module

public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Infra.Level.OrderIso

/-! # Domains for the outer observation comparison

The normalized diagonal is the outer cylinder. The lemmas below use the
literal sideways domains, without asserting `IsSolution` in that chart.
Source: `charged_SF_new_version.tex:L2332–L2355`, L2541–L2544; approved internal project record
(D1)–(D3).
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global

/-- [internal]
A dependence triangle based at a point of the sideways window stays in that
window. This assertion concerns the normalized coordinate order only. -/
theorem sidewaysTriangle_subtriangle {a b u v : ℝ}
    (hp : (u, v) ∈ sidewaysTriangle a b) :
    sidewaysTriangle v u ⊆ sidewaysTriangle a b := by
  rintro ⟨s, t⟩ ⟨hvt, hts, hsu⟩
  exact ⟨hp.1.trans hvt, hts, hsu.trans hp.2.2⟩

/-- [internal]
An incoming integration from the cylinder stays in its dependence triangle. -/
theorem sidewaysTriangle_incoming {u v s : ℝ} (hs : s ∈ Icc v u) :
    (s, v) ∈ sidewaysTriangle v u := ⟨le_rfl, hs.1, hs.2⟩

/-- [internal]
An outward Maxwell integration stays in its dependence triangle. -/
theorem sidewaysTriangle_outgoing {u v t : ℝ} (ht : t ∈ Icc v u) :
    (u, t) ∈ sidewaysTriangle v u := ⟨ht.1, ht.2, le_rfl⟩

/-- [internal]
The normalized sideways triangle is compact, including a degenerate window. -/
theorem isCompact_sidewaysTriangle (a b : ℝ) : IsCompact (sidewaysTriangle a b) := by
  have hc : IsClosed (sidewaysTriangle a b) :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  apply (show IsCompact (Icc a b ×ˢ Icc a b) from
    isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
  intro p hp
  exact ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩, ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩

/-- [internal]
Moving the radial cutoff inward enlarges the actual truncated sideways set. -/
theorem sidewaysTruncation_mono_radius (S : Fields) (D : Set (ℝ × ℝ))
    (a b L : ℝ) {ρ σ : ℝ} (hρ : ρ ≤ σ) :
    sidewaysTruncation S D a b σ L ⊆ sidewaysTruncation S D a b ρ L := by
  intro p hp
  exact ⟨hp.1, ⟨hρ.trans hp.2.1, hp.2.2⟩⟩

/-- [internal]
Original-domain completeness is preserved when decreasing the original
outgoing label and increasing the original incoming label. -/
theorem origDomain_inward_rectangle {ui u v s t : ℝ}
    (hp : (u, v) ∈ origDomain ui) (hs : ui ≤ s) (hsu : s ≤ u)
    (hvt : v ≤ t) (ht : t ≤ 0) : (s, t) ∈ origDomain ui :=
  ⟨hs, hsu.trans_lt hp.2.1, hsu.trans (hp.2.2.1.trans hvt), ht⟩

/-- [internal]
The entire dependence triangle lies in the preimage of the original
development under increasing chart maps. The lower and upper chart bounds
are the proper endpoint bounds supplied by normalization. -/
theorem subtriangle_mem_original_of_normalization
    {F G : ℝ → ℝ} {ui a b u v : ℝ} (hF : MonotoneOn F (Icc a b))
    (hG : MonotoneOn G (Icc a b)) (hFa : ui ≤ F a) (hGb : G b ≤ 0)
    (hp : (u, v) ∈ sidewaysTriangle a b)
    (horig : (F u, G v) ∈ origDomain ui) :
    ∀ p ∈ sidewaysTriangle v u, (F p.1, G p.2) ∈ origDomain ui := by
  intro p hp'
  have huv : u ∈ Icc a b := ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hv : v ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hs : p.1 ∈ Icc a b :=
    ⟨hp.1.trans (hp'.1.trans hp'.2.1), hp'.2.2.trans hp.2.2⟩
  have ht : p.2 ∈ Icc a b :=
    ⟨hp.1.trans hp'.1, (hp'.2.1.trans hp'.2.2).trans hp.2.2⟩
  exact origDomain_inward_rectangle horig
    (hFa.trans (hF ⟨le_rfl, huv.1.trans huv.2⟩ hs hs.1))
    (hF hs huv hp'.2.2) (hG hv ht hp'.1)
    ((hG ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2).trans hGb)

/-- [internal]
Radius monotonicity on the two null sections puts the dependence triangle
above its tip's radius. These are the two monotonicity conclusions of the
normalized radius equations, with their exact section domains. -/
theorem subtriangle_radius_le_of_normalization {S : Fields} {u v : ℝ}
    (hin : AntitoneOn (fun s => S.r s v) (Icc v u))
    (hout : ∀ s ∈ Icc v u, MonotoneOn (S.r s) (Icc v s)) :
    ∀ p ∈ sidewaysTriangle v u, S.r u v ≤ S.r p.1 p.2 := by
  intro p hp
  have hs : p.1 ∈ Icc v u := ⟨hp.1.trans hp.2.1, hp.2.2⟩
  exact (hin hs ⟨hs.1.trans hs.2, le_rfl⟩ hs.2).trans
    (hout p.1 hs ⟨le_rfl, hs.1⟩ ⟨hp.1, hp.2.1⟩ hp.1)

/-- [internal]
Every incoming scalar path and every outward Maxwell path lies in the same
actual radius truncation as its endpoint. This is a direct consumer of the
full dependence-triangle inclusion, with no enlarged window. -/
theorem sidewaysTruncation_paths {S : Fields} {D : Set (ℝ × ℝ)}
    {a b u v rho L : ℝ}
    (hsub : sidewaysTriangle v u ⊆ sidewaysTruncation S D a b rho L) :
    (∀ s ∈ Icc v u, (s, v) ∈ sidewaysTruncation S D a b rho L) ∧
      (∀ t ∈ Icc v u, (u, t) ∈ sidewaysTruncation S D a b rho L) :=
  ⟨fun _ hs => hsub (sidewaysTriangle_incoming hs),
    fun _ ht => hsub (sidewaysTriangle_outgoing ht)⟩

/-- [internal]
Canonical outgoing radial coordinates on a closed proper section, including
their endpoint values. The inverse is constructed from the actual interval
order isomorphism, with the canonical constant extension outside its image.
The radial derivative is asserted only in the open interval. No arbitrary
inverse, solution continuation or normalized `IsSolution` is used. -/
theorem radial_section_inverse_of_normalization {R lam : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn R (Icc a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt R (lam s) s)
    (hlam : ∀ s ∈ Ioo a b, 0 < lam s) :
    ∃ inv : ℝ → ℝ,
      StrictMonoOn R (Icc a b) ∧ Continuous inv ∧ (∀ r, inv r ∈ Icc a b) ∧
      (∀ r ∈ Icc (R a) (R b), R (inv r) = r) ∧
      inv (R a) = a ∧ inv (R b) = b ∧
      ∀ r ∈ Ioo (R a) (R b), inv r ∈ Ioo a b ∧
        HasDerivAt inv (lam (inv r))⁻¹ r := by
  have hm : StrictMonoOn R (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    intro s hs
    have hs' : s ∈ Ioo a b := by simpa only [interior_Icc] using hs
    rw [(hd s hs').deriv]
    exact hlam s hs'
  let e := Level.intervalOrderIso hab hc hm
  have hRab : R a ≤ R b := hm.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let inv := Level.intervalInverse e hRab
  have he (x : Icc a b) : (e x : ℝ) = R x := Level.intervalOrderIso_apply hab hc hm x
  have hi (r : ℝ) (hr : r ∈ Icc (R a) (R b)) : R (inv r) = r := by
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨r, hr⟩)
    simpa only [he, ← Level.intervalInverse_apply e hRab ⟨r, hr⟩] using h
  have hiR (x : ℝ) (hx : x ∈ Icc a b) : inv (R x) = x := by
    have h := Level.intervalInverse_apply_apply e hRab ⟨x, hx⟩
    simpa only [he] using h
  refine ⟨inv, hm, Level.continuous_intervalInverse e hRab,
    Level.intervalInverse_mem e hRab, hi, hiR a ⟨le_rfl, hab⟩,
    hiR b ⟨hab, le_rfl⟩, ?_⟩
  intro r hr
  have hmem : inv r ∈ Icc a b := Level.intervalInverse_mem e hRab r
  have hin : inv r ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
    · intro heq
      have hh := hi r ⟨hr.1.le, hr.2.le⟩
      rw [← heq] at hh
      exact hr.1.ne hh
    · intro heq
      have hh := hi r ⟨hr.1.le, hr.2.le⟩
      rw [heq] at hh
      exact hr.2.ne hh.symm
  refine ⟨hin, ?_⟩
  have hdi := Level.hasDerivWithinAt_intervalInverse_of_deriv e hRab he
    ⟨hr.1.le, hr.2.le⟩ (hd (inv r) hin).hasDerivWithinAt (hlam (inv r) hin).ne'
  exact hdi.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

/-- [internal]
Pointwise control by the literal region supremum. This works for an empty
region and does not convert an unproved-finite extended real to a real. -/
theorem enorm_le_comparisonNorm {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {p : ℝ × ℝ} (hp : p ∈ D) :
    ‖f p.1 p.2‖ₑ ≤ comparisonNorm D f :=
  le_iSup_of_le p (le_iSup_of_le hp le_rfl)

/-- [internal]
A real upper bound on a region bounds its extended-real comparison norm. -/
theorem comparisonNorm_le_of_bound {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ p ∈ D, ‖f p.1 p.2‖ ≤ C) :
    comparisonNorm D f ≤ ENNReal.ofReal C := by
  refine iSup_le fun p => iSup_le fun hp => ?_
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (h p hp)

/-- [internal]
A finite real comparison-norm bound controls every actual point, without
converting an unproved-finite extended real using `toReal`. -/
theorem norm_le_of_comparisonNorm_le {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {C : ℝ} {p : ℝ × ℝ}
    (hC : 0 ≤ C) (hp : p ∈ D) (h : comparisonNorm D f ≤ ENNReal.ofReal C) :
    ‖f p.1 p.2‖ ≤ C := by
  have hh := (enorm_le_comparisonNorm (f := f) hp).trans h
  rw [← ofReal_norm] at hh
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hh

/-- [internal]
A continuous field on a nonempty compact region attains its literal
extended-real comparison norm. In particular that norm is finite. -/
theorem comparisonNorm_eq_ofReal_max {E : Type*} [NormedAddCommGroup E]
    {K : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} (hK : IsCompact K)
    (hne : K.Nonempty) (hf : ContinuousOn (Function.uncurry f) K) :
    ∃ p ∈ K, comparisonNorm K f = ENNReal.ofReal ‖f p.1 p.2‖ ∧
      sSup ((fun q : ℝ × ℝ => ‖f q.1 q.2‖) '' K) = ‖f p.1 p.2‖ := by
  obtain ⟨p, hp, heq, hmax⟩ := hK.exists_sSup_image_eq_and_ge hne hf.norm
  refine ⟨p, hp, le_antisymm ?_ ?_, heq⟩
  · exact comparisonNorm_le_of_bound (norm_nonneg _) hmax
  · simpa only [ofReal_norm] using (enorm_le_comparisonNorm (f := f) hp)

/-- [internal]
Strictly decreasing incoming radius and inclusion of the whole dependence
triangle approximate every interior-radius point from larger radius.
The normalized diagonal has radius `L`, the outer-cylinder radius. -/
theorem radius_raise_closure_of_normalization {S : Fields}
    {K : Set (ℝ × ℝ)} {L : ℝ}
    (horder : ∀ p ∈ K, p.2 ≤ p.1)
    (htriangle : ∀ p ∈ K, sidewaysTriangle p.2 p.1 ⊆ K)
    (hdiag : ∀ p ∈ K, S.r p.2 p.2 = L)
    (hin : ∀ p ∈ K, StrictAntiOn (fun u => S.r u p.2) (Icc p.2 p.1)) :
    ∀ p ∈ K, S.r p.1 p.2 < L →
      p ∈ closure {q ∈ K | S.r p.1 p.2 < S.r q.1 q.2} := by
  intro p hp hr
  have hlt : p.2 < p.1 := by
    refine lt_of_le_of_ne (horder p hp) ?_
    intro heq
    rw [← heq, hdiag p hp] at hr
    exact (lt_irrefl _ hr)
  have hcl : p.1 ∈ closure (Ico p.2 p.1) := by
    rw [closure_Ico hlt.ne]
    exact ⟨hlt.le, le_rfl⟩
  have hc : Continuous (fun u : ℝ => (u, p.2)) := continuous_id.prodMk continuous_const
  have hm := mem_closure_image hc.continuousAt hcl
  change (p.1, p.2) ∈ closure ((fun u : ℝ => (u, p.2)) '' Ico p.2 p.1) at hm
  apply closure_mono (s := (fun u : ℝ => (u, p.2)) '' Ico p.2 p.1) ?_ hm
  rintro q ⟨u, hu, rfl⟩
  exact ⟨htriangle p hp ⟨le_rfl, hu.1, hu.2.le⟩,
    hin p hp ⟨hu.1, hu.2.le⟩ ⟨hlt.le, le_rfl⟩ hu.2⟩

/-- [internal]
Strict incoming radius decrease identifies the radius-`L` cutoff with
the normalized diagonal, so cylinder boundary data control the initial
depth maximum on its literal region. -/
theorem radius_eq_outer_iff_diagonal_of_normalization {S : Fields}
    {K : Set (ℝ × ℝ)} {L : ℝ}
    (horder : ∀ p ∈ K, p.2 ≤ p.1) (hdiag : ∀ p ∈ K, S.r p.2 p.2 = L)
    (hin : ∀ p ∈ K, StrictAntiOn (fun u => S.r u p.2) (Icc p.2 p.1)) :
    ∀ p ∈ K, S.r p.1 p.2 = L ↔ p.1 = p.2 := by
  intro p hp
  constructor
  · intro heq
    by_contra hne
    have hlt : p.2 < p.1 := lt_of_le_of_ne (horder p hp) (Ne.symm hne)
    have hh := hin p hp ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
    dsimp only at hh
    rw [heq, hdiag p hp] at hh
    exact lt_irrefl _ hh
  · intro heq
    simpa only [heq] using hdiag p hp

private theorem continuousOn_radial_sSup {K : Set (ℝ × ℝ)} {r h : (ℝ × ℝ) → ℝ}
    {L dmax : ℝ} (hK : IsCompact K) (hr : ContinuousOn r K)
    (hh : ContinuousOn h K) (hbase : ∃ p ∈ K, r p = L)
    (hraise : ∀ p ∈ K, r p < L → p ∈ closure {q ∈ K | r p < r q}) :
    ContinuousOn (fun d => sSup (h '' (K ∩ {p | L - d ≤ r p}))) (Icc 0 dmax) := by
  let cuts := fun d : ℝ => K ∩ {p | L - d ≤ r p}
  have hcomp (d : ℝ) : IsCompact (cuts d) :=
    hK.of_isClosed_subset
      (hr.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici) inter_subset_left
  have hne (d : ℝ) (hd : 0 ≤ d) : (cuts d).Nonempty := by
    obtain ⟨p, hp, heq⟩ := hbase
    exact ⟨p, hp, by dsimp; rw [heq]; linarith only [hd]⟩
  have hmax (d : ℝ) (hd : 0 ≤ d) : ∃ p ∈ cuts d,
      sSup (h '' cuts d) = h p ∧ ∀ q ∈ cuts d, h q ≤ h p :=
    (hcomp d).exists_sSup_image_eq_and_ge (hne d hd) (hh.mono inter_subset_left)
  intro d hd
  apply continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
  constructor
  · intro b hb
    obtain ⟨p, hp, heq, _⟩ := hmax d hd.1
    change b < sSup (h '' cuts d) at hb
    rw [heq] at hb
    by_cases hd0 : d = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      obtain ⟨q, hq, heq', hmax'⟩ := hmax t ht.1
      change b < sSup (h '' cuts t)
      rw [heq']
      apply hb.trans_le (hmax' p ?_)
      refine ⟨hp.1, ?_⟩
      have hpr := hp.2
      dsimp [cuts] at hpr ⊢
      rw [hd0] at hpr
      linarith only [hpr, ht.1]
    · have hq : ∃ q ∈ K, L - d < r q ∧ b < h q := by
        by_cases hstrict : L - d < r p
        · exact ⟨p, hp.1, hstrict, hb⟩
        · have heqr : r p = L - d := le_antisymm (le_of_not_gt hstrict) hp.2
          have hdpos : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm hd0)
          have hpr : r p < L := by linarith only [heqr, hdpos]
          by_contra! hn
          have hle : h p ≤ b := ContinuousWithinAt.closure_le (hraise p hp.1 hpr)
            ((hh p hp.1).mono (by intro q hq; exact hq.1)) continuousWithinAt_const
            (by intro q hq; exact hn q hq.1 (by rw [← heqr]; exact hq.2))
          exact (not_le_of_gt hb) hle
      obtain ⟨q, hq, hrq, hbq⟩ := hq
      have hevent : ∀ᶠ t in 𝓝[Icc 0 dmax] d, L - t < r q :=
        ((continuous_const.sub continuous_id).continuousAt.eventually
          (gt_mem_nhds hrq)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hevent] with t ht hrt
      obtain ⟨p, hp, heq, hmax'⟩ := hmax t ht.1
      change b < sSup (h '' cuts t)
      rw [heq]
      exact hbq.trans_le (hmax' q ⟨hq, hrt.le⟩)
  · intro b hb
    let bad := {p ∈ K | b ≤ h p}
    have hbad : IsCompact bad := hK.of_isClosed_subset
      (hh.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici) (by intro p hp; exact hp.1)
    by_cases hbadne : bad.Nonempty
    · obtain ⟨q, hq, hqmax⟩ := hbad.exists_isMaxOn hbadne
        (hr.mono (by intro p hp; exact hp.1))
      have hrq : r q < L - d := by
        by_contra! hn
        obtain ⟨p, hp, heq, hmax'⟩ := hmax d hd.1
        change sSup (h '' cuts d) < b at hb
        rw [heq] at hb
        exact (not_le_of_gt hb) (hq.2.trans (hmax' q ⟨hq.1, hn⟩))
      have hevent : ∀ᶠ t in 𝓝[Icc 0 dmax] d, r q < L - t :=
        ((continuous_const.sub continuous_id).continuousAt.eventually
          (lt_mem_nhds hrq)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hevent] with t ht hrt
      obtain ⟨p, hp, heq, _⟩ := hmax t ht.1
      change sSup (h '' cuts t) < b
      rw [heq]
      by_contra! hn
      exact (not_le_of_gt hrt) (hp.2.trans (hqmax ⟨hp.1, hn⟩))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      obtain ⟨p, hp, heq, _⟩ := hmax t ht.1
      change sSup (h '' cuts t) < b
      rw [heq]
      exact lt_of_not_ge (fun hn => hbadne ⟨p, hp.1, hn⟩)

/-- [internal]
Strict negativity of the normalized incoming radius derivative gives
strict antitonicity on every closed incoming dependence segment. -/
theorem strictAntiOn_radius_incoming_of_normalization {S : Fields}
    {K : Set (ℝ × ℝ)} (hr : ContinuousOn (Function.uncurry S.r) K)
    (htriangle : ∀ p ∈ K, sidewaysTriangle p.2 p.1 ⊆ K)
    (hderiv : ∀ p ∈ K, HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1)
    (hnu : ∀ p ∈ K, S.nu p.1 p.2 < 0) :
    ∀ p ∈ K, StrictAntiOn (fun u => S.r u p.2) (Icc p.2 p.1) := by
  intro p hp
  have hmem (u : ℝ) (hu : u ∈ Icc p.2 p.1) : (u, p.2) ∈ K :=
    htriangle p hp ⟨le_rfl, hu.1, hu.2⟩
  apply strictAntiOn_of_hasDerivWithinAt_neg (f' := fun u => S.nu u p.2) (convex_Icc _ _)
    (hr.comp (continuous_id.prodMk continuous_const).continuousOn hmem)
  · intro u hu
    exact (hderiv (u, p.2) (hmem u (interior_subset hu))).hasDerivWithinAt
  · intro u hu
    exact hnu (u, p.2) (hmem u (interior_subset hu))

/-- [internal]
At a depth in the permitted range, a literal sideways truncation equals
the closed radius cutoff of the fixed innermost compact region. -/
theorem sidewaysTruncation_depth_eq (S : Fields) (D : Set (ℝ × ℝ))
    (a b L₀ L : ℝ) {d : ℝ} (hd : d ∈ Icc 0 (L - L₀)) :
    sidewaysTruncation S D a b (L - d) L =
      sidewaysTruncation S D a b L₀ L ∩ {p | L - d ≤ S.r p.1 p.2} := by
  ext p
  constructor
  · intro hp
    exact ⟨⟨hp.1, ⟨by linarith only [hd.2, hp.2.1], hp.2.2⟩⟩, hp.2.1⟩
  · intro hp
    exact ⟨hp.1.1, hp.2, hp.1.2.2⟩

/-- [internal]
Both the real maximum and its literal extended-real comparison norm vary
continuously with depth on the actual compact sideways truncations.
Finiteness is proved by compact attainment before any real use of a norm.
All regularity and negative-derivative inputs are in the normalized chart. -/
theorem continuousOn_outer_radius_maximum {E : Type*} [NormedAddCommGroup E]
    {S : Fields} {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → E} {a b L₀ L : ℝ}
    (hK : IsCompact (sidewaysTruncation S D a b L₀ L))
    (hr : ContinuousOn (Function.uncurry S.r) (sidewaysTruncation S D a b L₀ L))
    (hf : ContinuousOn (Function.uncurry f) (sidewaysTruncation S D a b L₀ L))
    (hbase : ∃ p ∈ sidewaysTruncation S D a b L₀ L, S.r p.1 p.2 = L)
    (htriangle : ∀ p ∈ sidewaysTruncation S D a b L₀ L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b L₀ L)
    (hdiag : ∀ p ∈ sidewaysTruncation S D a b L₀ L, S.r p.2 p.2 = L)
    (hderiv : ∀ p ∈ sidewaysTruncation S D a b L₀ L,
      HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1)
    (hnu : ∀ p ∈ sidewaysTruncation S D a b L₀ L, S.nu p.1 p.2 < 0) :
    ContinuousOn (fun d => sSup ((fun p : ℝ × ℝ => ‖f p.1 p.2‖) ''
      sidewaysTruncation S D a b (L - d) L)) (Icc 0 (L - L₀)) ∧
    ContinuousOn (fun d => comparisonNorm (sidewaysTruncation S D a b (L - d) L) f)
      (Icc 0 (L - L₀)) ∧
    ∀ d ∈ Icc 0 (L - L₀),
      comparisonNorm (sidewaysTruncation S D a b (L - d) L) f =
        ENNReal.ofReal (sSup ((fun p : ℝ × ℝ => ‖f p.1 p.2‖) ''
          sidewaysTruncation S D a b (L - d) L)) := by
  let K := sidewaysTruncation S D a b L₀ L
  have hin := strictAntiOn_radius_incoming_of_normalization hr htriangle hderiv hnu
  have hraise := radius_raise_closure_of_normalization
    (fun p hp => hp.1.2.2.1) htriangle hdiag hin
  have hc := continuousOn_radial_sSup (dmax := L - L₀) hK hr hf.norm hbase hraise
  have hreal : ContinuousOn (fun d => sSup ((fun p : ℝ × ℝ => ‖f p.1 p.2‖) ''
      sidewaysTruncation S D a b (L - d) L)) (Icc 0 (L - L₀)) := by
    apply hc.congr
    intro d hd
    dsimp only
    rw [sidewaysTruncation_depth_eq S D a b L₀ L hd]
    rfl
  have heq (d : ℝ) (hd : d ∈ Icc 0 (L - L₀)) :
      comparisonNorm (sidewaysTruncation S D a b (L - d) L) f =
        ENNReal.ofReal (sSup ((fun p : ℝ × ℝ => ‖f p.1 p.2‖) ''
          sidewaysTruncation S D a b (L - d) L)) := by
    rw [sidewaysTruncation_depth_eq S D a b L₀ L hd]
    have hcomp : IsCompact (K ∩ {p | L - d ≤ S.r p.1 p.2}) :=
      hK.of_isClosed_subset
        (hr.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici) inter_subset_left
    have hne : (K ∩ {p | L - d ≤ S.r p.1 p.2}).Nonempty := by
      obtain ⟨p, hp, heq⟩ := hbase
      exact ⟨p, hp, by dsimp; rw [heq]; linarith only [hd.1]⟩
    obtain ⟨p, hp, heq, hmax⟩ := comparisonNorm_eq_ofReal_max hcomp hne
      (hf.mono inter_subset_left)
    rw [heq, hmax]
  exact ⟨hreal, (ENNReal.continuous_ofReal.comp_continuousOn hreal).congr
    (fun d hd => heq d hd), heq⟩

/-- [internal]
The derivative signs preserve the full dependence triangle at every larger
radial cutoff of a given complete normalized comparison region. Thus each
stopped estimate and every outgoing charge/mass segment uses its own set. -/
theorem subtriangle_mem_larger_radius_of_normalization {S : Fields}
    {D : Set (ℝ × ℝ)} {a b L₀ L : ℝ}
    (hr : ContinuousOn (Function.uncurry S.r) (sidewaysTruncation S D a b L₀ L))
    (htriangle : ∀ p ∈ sidewaysTruncation S D a b L₀ L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b L₀ L)
    (hrin : ∀ p ∈ sidewaysTruncation S D a b L₀ L,
      HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1)
    (hrout : ∀ p ∈ sidewaysTruncation S D a b L₀ L,
      HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2)
    (hnu : ∀ p ∈ sidewaysTruncation S D a b L₀ L, S.nu p.1 p.2 < 0)
    (hlam : ∀ p ∈ sidewaysTruncation S D a b L₀ L, 0 < S.lam p.1 p.2) :
    ∀ ρ, L₀ ≤ ρ → ∀ p ∈ sidewaysTruncation S D a b ρ L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b ρ L := by
  have hin := strictAntiOn_radius_incoming_of_normalization hr htriangle hrin hnu
  have hout (p) (hp : p ∈ sidewaysTruncation S D a b L₀ L) :
      MonotoneOn (S.r p.1) (Icc p.2 p.1) := by
    have hpath := (sidewaysTruncation_paths (htriangle p hp)).2
    apply StrictMonoOn.monotoneOn
    apply strictMonoOn_of_deriv_pos (f := S.r p.1) (convex_Icc _ _)
      (hr.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => hpath t ht))
    intro t ht
    have ht' : t ∈ Icc p.2 p.1 := interior_subset ht
    rw [(hrout (p.1, t) (hpath t ht')).deriv]
    exact hlam (p.1, t) (hpath t ht')
  intro ρ hρ p hp q hq
  have hpR := sidewaysTruncation_mono_radius S D a b L hρ hp
  have hqR := htriangle p hpR hq
  have hrad := subtriangle_radius_le_of_normalization (hin p hpR).antitoneOn
    (fun u hu => hout (u, p.2) (htriangle p hpR (sidewaysTriangle_incoming hu))) q hq
  exact ⟨hqR.1, hp.2.1.trans hrad, hqR.2.2⟩

namespace Observation

/-- [internal]
The temporary comparison bound gives a uniform bound for the shifted scalar
and mass difference. The scalar bound is `C + 1`, depending only on the static
outer scalar bound `C`; the mass bound is the universal number `4`.
The explicit mass and static estimates are normalization/static inputs. -/
theorem outer_bootstrap_box_of_normalization (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ)
        (phiStar : ℝ → ℂ) (mStar : ℝ → ℝ),
        comparisonNorm D (scalarComparison S H phiStar) ≤ 1 →
        (∀ p ∈ D, ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ ≤ C) →
        (∀ p ∈ D, S.m p.1 p.2 ∈ Icc 0 2) →
        (∀ p ∈ D, |mStar (S.r p.1 p.2)| ≤ 2) →
        (∀ p ∈ D, ‖shiftedRphi S H p.1 p.2‖ ≤ K) ∧
          comparisonNorm D (massComparison S mStar) ≤ 4 := by
  refine ⟨C + 1, by linarith only [hC], ?_⟩
  intro S D H phiStar mStar hw hstatic hm hmStar
  have hwb (p) (hp : p ∈ D) : ‖scalarComparison S H phiStar p.1 p.2‖ ≤ 1 := by
    have he := (enorm_le_comparisonNorm hp).trans hw
    simpa only [← ofReal_norm, ← ENNReal.ofReal_one,
      ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)] using he
  refine ⟨?_, ?_⟩
  · intro p hp
    calc
      ‖shiftedRphi S H p.1 p.2‖ =
          ‖scalarComparison S H phiStar p.1 p.2 +
            (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by
        congr 1
        simp only [scalarComparison, sub_add_cancel]
      _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ +
          ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := norm_add_le _ _
      _ ≤ C + 1 := by linarith only [hwb p hp, hstatic p hp]
  · suffices comparisonNorm D (massComparison S mStar) ≤ ENNReal.ofReal 4 by
      simpa using this
    apply comparisonNorm_le_of_bound (by norm_num : (0 : ℝ) ≤ 4)
    intro p hp
    change ‖S.m p.1 p.2 - mStar (S.r p.1 p.2)‖ ≤ 4
    calc
      ‖S.m p.1 p.2 - mStar (S.r p.1 p.2)‖ ≤
          ‖S.m p.1 p.2‖ + ‖mStar (S.r p.1 p.2)‖ := norm_sub_le _ _
      _ ≤ 4 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hm p hp).1, Real.norm_eq_abs]
        linarith only [(hm p hp).2, hmStar p hp]

end Observation

end EmcsfAcExtension.Global
