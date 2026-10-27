module

public import EmcsfAcExtension.Global.Exterior.FrontierTransport
public import EmcsfAcExtension.Infra.Level.OrderIso
import Mathlib.Topology.Order.Compact

/-! # The actual outgoing field supremum

The supremum is over the genuine moving exterior interval. Its continuity
comes from parametrizing that compact interval by a fixed unit interval.
No derivative supremum or uniform modulus of the rough density is used.
Source: `charged_SF_new_version.tex:L1356–L1360`, approved internal project record (I1)–(I2).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The actual supremum of `|theta/lambda|` on the moving exterior row. -/
@[expose] noncomputable def outgoingFieldSup (S : Fields) (t : ℝ → ℝ) (u : ℝ) : ℝ :=
  sSup ((fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) '' Icc (t u) 0)

/-- [internal]
Compact supremum continuity for a moving interval with continuous left
endpoint. There is no quantitative continuity-modulus premise. -/
theorem continuousOn_moving_interval_sup {c : ℝ} {t : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (ht : ContinuousOn t (Ico c 0)) (ht0 : ∀ u ∈ Ico c 0, t u ≤ 0)
    (hf : ContinuousOn f.uncurry {p | p.1 ∈ Ico c 0 ∧ p.2 ∈ Icc (t p.1) 0}) :
    ContinuousOn (fun u => sSup (f u '' Icc (t u) 0)) (Ico c 0) := by
  let U := Ico c 0
  let Z := Icc (0 : ℝ) 1
  let F : U → Z → ℝ := fun u z => f u (t u * (1 - z))
  have hm (u : U) (z : Z) : t u * (1 - z) ∈ Icc (t u) 0 := by
    have htu := ht0 u u.property
    have hz := z.property
    have h₁ := mul_nonpos_of_nonpos_of_nonneg htu hz.1
    have h₂ := mul_nonpos_of_nonpos_of_nonneg htu (sub_nonneg.mpr hz.2)
    constructor <;> nlinarith only [h₁, h₂]
  have he (u : U) : range (F u) = f u '' Icc (t u) 0 := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, hm u z, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      by_cases htu : t u = 0
      · have hv0 : v = 0 := by simpa only [htu, Icc_self, mem_singleton_iff] using hv
        refine ⟨⟨0, by dsimp [Z]; norm_num⟩, ?_⟩
        simp only [F, htu, hv0, zero_mul]
      · have htn : 0 < -t u := neg_pos.mpr (lt_of_le_of_ne (ht0 u u.property) htu)
        let z : Z := ⟨(v - t u) / (-t u),
          div_nonneg (sub_nonneg.mpr hv.1) htn.le,
          (div_le_iff₀ htn).2 (by linarith only [hv.2])⟩
        refine ⟨z, ?_⟩
        have hh : t u * (1 - (v - t u) / (-t u)) = v := by field_simp [htu]; ring
        simp only [F, z, hh]
  have cu : Continuous (fun p : U × Z => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have cz : Continuous (fun p : U × Z => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have ct : Continuous (fun p : U × Z => t p.1) := ht.domRestrict.comp continuous_fst
  have cm : Continuous (fun p : U × Z => ((p.1 : ℝ), t p.1 * (1 - (p.2 : ℝ)))) :=
    cu.prodMk (ct.mul (continuous_const.sub cz))
  have cF : Continuous F.uncurry := hf.comp_continuous cm (fun p => ⟨p.1.property, hm p.1 p.2⟩)
  have cs : Continuous (fun u : U => sSup (F u '' univ)) :=
    isCompact_univ.continuous_sSup cF
  rw [continuousOn_iff_continuous_domRestrict]
  convert cs using 1
  funext u
  rw [image_univ, he]
  rfl

/-- [internal]
The genuine outgoing field supremum is continuous along any continuous
proper frontier. Only undifferentiated solution fields occur. -/
theorem outgoingFieldSup_continuousOn {ui e c : ℝ} {S : Fields} {t : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : ui ≤ c) (ht : ContinuousOn t (Ico c 0))
    (hrange : ∀ u ∈ Ico c 0, u < t u ∧ t u ≤ 0) :
    ContinuousOn (outgoingFieldSup S t) (Ico c 0) := by
  apply continuousOn_moving_interval_sup ht (fun u hu => (hrange u hu).2)
  let K := {p : ℝ × ℝ | p.1 ∈ Ico c 0 ∧ p.2 ∈ Icc (t p.1) 0}
  have hK : K ⊆ origDomain ui := by
    intro p hp
    exact ⟨hc.trans hp.1.1, hp.1.2, (hrange p.1 hp.1).1.le.trans hp.2.1, hp.2.2⟩
  have cl := h.solution.cont_lam.mono hK
  exact ((h.solution.cont_theta.mono hK).div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr
      (h.solution.lam_pos p (hK hp)).ne')).norm

/-- [internal]
A uniform exterior field bound controls the actual moving-row supremum,
which is nonnegative and bounds every field value on that row. The bound
`B` is fixed before all rows and labels; the comparison coefficient is `1`. -/
theorem outgoingFieldSup_bounds {ui e c B : ℝ} {S : Fields} {t ell : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : ui ≤ c)
    (hroot : ∀ u ∈ Ico c 0, u < t u ∧ t u ≤ 0 ∧ S.r u (t u) = ell (S.r u 0))
    (hfield : ∀ p ∈ adaptiveExterior S ui c ell,
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ≤ B) :
    ∀ u ∈ Ico c 0, 0 ≤ outgoingFieldSup S t u ∧ outgoingFieldSup S t u ≤ B ∧
      ∀ v ∈ Icc (t u) 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ outgoingFieldSup S t u := by
  intro u hu
  have ht := hroot u hu
  have hs : outSeg u (t u) 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff ht.2.1).2 ⟨hc.trans hu.1, hu.2, ht.1.le, le_rfl⟩
  have hb (v : ℝ) (hv : v ∈ Icc (t u) 0) :
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ B := by
    apply hfield (u, v)
    refine ⟨hs ⟨rfl, hv⟩, hu.1, ?_⟩
    rw [← ht.2.2]
    exact outgoing_radius_mono h ht.1.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
  have hB : BddAbove ((fun v => ‖S.theta u v / (S.lam u v : ℂ)‖) '' Icc (t u) 0) :=
    ⟨B, by rintro _ ⟨v, hv, rfl⟩; exact hb v hv⟩
  have hlo (v : ℝ) (hv : v ∈ Icc (t u) 0) :
      ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ outgoingFieldSup S t u :=
    le_csSup hB ⟨v, hv, rfl⟩
  refine ⟨(norm_nonneg _).trans (hlo 0 ⟨ht.2.1, le_rfl⟩), ?_, hlo⟩
  exact csSup_le ⟨_, ⟨0, ⟨ht.2.1, le_rfl⟩, rfl⟩⟩ (by rintro _ ⟨v, hv, rfl⟩; exact hb v hv)

end EmcsfAcExtension.Global.Exterior
