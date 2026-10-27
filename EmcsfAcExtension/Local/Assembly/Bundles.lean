module

public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Frozen.CovVarIn
public import EmcsfAcExtension.Frozen.JOut
public import EmcsfAcExtension.Frozen.KIn
public import EmcsfAcExtension.Frozen.Fields.Omega2
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Frozen.Fields.EqOn

import EmcsfAcExtension.Local.Api.EqOn

/-! # Frozen conclusion bundles for assembly

Literal internal definitions from internal project record; the frozen source
objects and theorem anchors are unchanged.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The existence bounds of the frozen anchor, as one bundle (exact frozen text; used only to
shorten the assembly). -/
@[expose] def ExistenceBounds (C e T : ℝ) (h : ℝ → ℂ) (S : Fields) : Prop :=
  (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
  (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
  AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
  (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
      (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤
    ENNReal.ofReal (C * datumVar h T) ∧
  (∀ p ∈ triangle 0 T,
    ‖S.phi p.1 p.2‖ ≤ 1 + ‖h 0‖ + 10 * datumVar h T ∧
    ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤
      C * datumVar h T ∧
    |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤
      C * datumVar h T ^ 2 ∧
    |S.Q p.1 p.2| ≤
      C * |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * datumVar h T * S.r p.1 p.2 ^ 2) ∧
  (∀ u ∈ Icc 0 T,
    eVariationOn (S.lam u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (S.nu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (S.mu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (S.Omega2 u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
  (∀ v ∈ Icc 0 T,
    eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
    eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤
      ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
  (∀ u ∈ Icc 0 T,
    AbsolutelyContinuousOnInterval (S.lam u) u T ∧
    AbsolutelyContinuousOnInterval (S.nu u) u T ∧
    AbsolutelyContinuousOnInterval (S.mu u) u T ∧
    AbsolutelyContinuousOnInterval (S.Omega2 u) u T) ∧
  (∀ v ∈ Icc 0 T,
    AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v ∧
    AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v ∧
    AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v ∧
    AbsolutelyContinuousOnInterval (fun u => S.Omega2 u v) 0 v) ∧
  ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle 0 T) ∧
  (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) ≤
    ENNReal.ofReal (C * datumVar h T)

/-- The stability conclusion of the frozen anchor, as one bundle (exact frozen text). -/
@[expose] def StabConclusion (C e T : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields) : Prop :=
  (∃ J K : ℝ → ℝ, IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
    (∀ u ∈ Icc 0 T, ∀ᵐ v ∂(volume.restrict (Icc u T)),
      ‖jOut S₁ u v - jOut S₂ u v‖ ≤ J v) ∧
    (∀ v ∈ Icc 0 T, ∀ᵐ u ∂(volume.restrict (Icc 0 v)),
      ‖kIn e S₁ u v - kIn e S₂ u v‖ ≤ K u) ∧
    ∀ p₁ ∈ triangle 0 T, ∀ p₂ ∈ triangle 0 T, ∀ p₃ ∈ triangle 0 T, ∀ p₄ ∈ triangle 0 T,
      (∫ v in (0 : ℝ)..T, J v) + (∫ u in (0 : ℝ)..T, K u) +
        (|S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| + |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| +
          |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2) +
        ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ + ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
        ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ ≤
      C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)) ∧
  (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
      (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
    ENNReal.ofReal (C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T))

/-- Enlarge the universal bound constant in the existence conclusion.
This is an internal assembly helper; `C` and `C'` are independent of the data. -/
theorem ExistenceBounds.mono {C C' e T : ℝ} {h : ℝ → ℂ} {S : Fields}
    (hCC : C ≤ C') (hb : ExistenceBounds C e T h S) : ExistenceBounds C' e T h S := by
  have hε : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hc : C * datumVar h T ≤ C' * datumVar h T :=
    mul_le_mul_of_nonneg_right hCC hε
  have hc2 : C * datumVar h T ^ 2 ≤ C' * datumVar h T ^ 2 :=
    mul_le_mul_of_nonneg_right hCC (sq_nonneg _)
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  refine ⟨b1, b2, b3, b4.trans (ENNReal.ofReal_le_ofReal hc), ?_, ?_, ?_,
    b8, b9, b10, b11.trans (ENNReal.ofReal_le_ofReal hc)⟩
  · intro p hp
    obtain ⟨hphi, hratio, hgeom, hQ⟩ := b5 p hp
    refine ⟨hphi, hratio.trans hc, hgeom.trans hc2, hQ.trans ?_⟩
    gcongr
  · intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := b6 u hu
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal hc2),
      h2.trans (ENNReal.ofReal_le_ofReal hc2), h3.trans (ENNReal.ofReal_le_ofReal hc2),
      h4.trans (ENNReal.ofReal_le_ofReal hc2)⟩
  · intro v hv
    obtain ⟨h1, h2, h3, h4⟩ := b7 v hv
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal hc2),
      h2.trans (ENNReal.ofReal_le_ofReal hc2), h3.trans (ENNReal.ofReal_le_ofReal hc2),
      h4.trans (ENNReal.ofReal_le_ofReal hc2)⟩

/-- Transport the frozen existence bounds along equality on the full triangle.
The bound constant is retained, uniformly in the datum and both configurations.
The nonnegative terminal label ensures the axis AC interval lies in the triangle. -/
theorem ExistenceBounds.congr {C e T : ℝ} {h : ℝ → ℂ} {S S' : Fields}
    (hT : 0 ≤ T) (he : S.EqOn S' (triangle 0 T)) (hb : ExistenceBounds C e T h S') :
    ExistenceBounds C e T h S := by
  have hAC {E : Type} [PseudoMetricSpace E] {f g : ℝ → E} {a b : ℝ}
      (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
      (hfg : Set.EqOn g f (Icc a b)) : AbsolutelyContinuousOnInterval g a b :=
    hf.congr (by simpa only [uIcc_of_le hab] using hfg.symm)
  have hout (u : ℝ) (hu : u ∈ Icc 0 T) (v : ℝ) (hv : v ∈ Icc u T) :
      (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
  have hin (v : ℝ) (hv : v ∈ Icc 0 T) (u : ℝ) (hu : u ∈ Icc 0 v) :
      (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
  have htvout {E : Type} [PseudoEMetricSpace E] {f g : ℝ → ℝ → E}
      (hfg : ∀ p ∈ triangle 0 T, f p.1 p.2 = g p.1 p.2)
      (u : ℝ) (hu : u ∈ Icc 0 T) :
      eVariationOn (f u) (Icc u T) = eVariationOn (g u) (Icc u T) :=
    eVariationOn.eq_of_eqOn (fun v hv => hfg (u, v) (hout u hu v hv))
  have htvin {E : Type} [PseudoEMetricSpace E] {f g : ℝ → ℝ → E}
      (hfg : ∀ p ∈ triangle 0 T, f p.1 p.2 = g p.1 p.2)
      (v : ℝ) (hv : v ∈ Icc 0 T) :
      eVariationOn (fun u => f u v) (Icc 0 v) =
        eVariationOn (fun u => g u v) (Icc 0 v) :=
    eVariationOn.eq_of_eqOn (fun u hu => hfg (u, v) (hin v hv u hu))
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    b10.congr (fun p hp => he.r hp), ?_⟩
  · intro u hu
    exact hAC hu.2 (b1 u hu) (fun v hv => he.a (hout u hu v hv))
  · intro v hv
    exact hAC hv.1 (b2 v hv) (fun u hu => he.b (hin v hv u hu))
  · exact hAC hT b3 (fun t ht => he.phi ⟨ht.1, le_rfl, ht.2⟩)
  · have ho : (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) =
        ⨆ u ∈ Icc 0 T, eVariationOn (S'.a u) (Icc u T) :=
      iSup_congr fun u => iSup_congr fun hu => he.eVariationOn_a (hout u hu)
    have hi : (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) =
        ⨆ v ∈ Icc 0 T, covVarIn e S'.A S'.b 0 v v :=
      iSup_congr fun v => iSup_congr fun hv => he.covVarIn_b (hin v hv)
    simpa only [ho, hi] using b4
  · intro p hp
    simpa only [he.phi hp, he.theta hp, he.lam hp, he.xi hp, he.nu hp, he.mu hp,
      he.Q hp, he.r hp] using b5 p hp
  · intro u hu
    simpa only [htvout (fun _ hp => he.lam hp) u hu,
      htvout (fun _ hp => he.nu hp) u hu, htvout (fun _ hp => he.mu hp) u hu,
      htvout (fun _ hp => he.Omega2 hp) u hu] using b6 u hu
  · intro v hv
    simpa only [htvin (fun _ hp => he.lam hp) v hv,
      htvin (fun _ hp => he.nu hp) v hv, htvin (fun _ hp => he.mu hp) v hv,
      htvin (fun _ hp => he.Omega2 hp) v hv] using b7 v hv
  · intro u hu
    obtain ⟨hl, hn, hm, hO⟩ := b8 u hu
    exact ⟨hAC hu.2 hl (fun v hv => he.lam (hout u hu v hv)),
      hAC hu.2 hn (fun v hv => he.nu (hout u hu v hv)),
      hAC hu.2 hm (fun v hv => he.mu (hout u hu v hv)),
      hAC hu.2 hO (fun v hv => he.Omega2 (hout u hu v hv))⟩
  · intro v hv
    obtain ⟨hl, hn, hm, hO⟩ := b9 v hv
    exact ⟨hAC hv.1 hl (fun u hu => he.lam (hin v hv u hu)),
      hAC hv.1 hn (fun u hu => he.nu (hin v hv u hu)),
      hAC hv.1 hm (fun u hu => he.mu (hin v hv u hu)),
      hAC hv.1 hO (fun u hu => he.Omega2 (hin v hv u hu))⟩
  · have hi : (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) =
        ⨆ v ∈ Icc 0 T, eVariationOn (fun u => S'.b u v) (Icc 0 v) :=
      iSup_congr fun v => iSup_congr fun hv => he.eVariationOn_b (hin v hv)
    simpa only [hi] using b11

/-- Enlarge the universal bound constant in the stability conclusion.
This is an internal assembly helper; `C` and `C'` are independent of the data. -/
theorem StabConclusion.mono {C C' e T : ℝ} {h₁ h₂ : ℝ → ℂ} {S₁ S₂ : Fields}
    (hCC : C ≤ C') (hb : StabConclusion C e T h₁ h₂ S₁ S₂) :
    StabConclusion C' e T h₁ h₂ S₁ S₂ := by
  have hΔ : 0 ≤ ‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T :=
    add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hc := mul_le_mul_of_nonneg_right hCC hΔ
  obtain ⟨⟨J, K, hJ, hK, hj, hk, hmain⟩, htv⟩ := hb
  exact ⟨⟨J, K, hJ, hK, hj, hk, fun p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄ =>
    (hmain p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄).trans hc⟩,
    htv.trans (ENNReal.ofReal_le_ofReal hc)⟩

/-- Transport the frozen stability conclusion along equality on the full triangle.
The same constant and the same two integrable envelope witnesses are retained. -/
theorem StabConclusion.congr {C e T : ℝ} {h₁ h₂ : ℝ → ℂ} {S₁ S₂ S₁' S₂' : Fields}
    (e₁ : S₁.EqOn S₁' (triangle 0 T)) (e₂ : S₂.EqOn S₂' (triangle 0 T))
    (hb : StabConclusion C e T h₁ h₂ S₁' S₂') : StabConclusion C e T h₁ h₂ S₁ S₂ := by
  obtain ⟨⟨J, K, hJ, hK, hj, hk, hmain⟩, htv⟩ := hb
  refine ⟨⟨J, K, hJ, hK, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu
    have hs : ∀ v ∈ Icc u T, (u, v) ∈ triangle 0 T :=
      fun v hv => ⟨hu.1, hv.1, hv.2⟩
    filter_upwards [e₁.jOut_ae hs, e₂.jOut_ae hs, hj u hu] with v hv₁ hv₂ hv
    simpa only [hv₁, hv₂] using hv
  · intro v hv
    have hs : ∀ u ∈ Icc 0 v, (u, v) ∈ triangle 0 T :=
      fun u hu => ⟨hu.1, hu.2, hv.2⟩
    filter_upwards [e₁.kIn_ae (e := e) hs, e₂.kIn_ae (e := e) hs, hk v hv]
      with u hu₁ hu₂ hu
    simpa only [hu₁, hu₂] using hu
  · intro p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
    simpa only [e₁.lam hp₁, e₂.lam hp₁, e₁.nu hp₁, e₂.nu hp₁, e₁.r hp₁,
      e₂.r hp₁, e₁.a hp₂, e₂.a hp₂, e₁.b hp₃, e₂.b hp₃, e₁.phi hp₄,
      e₂.phi hp₄] using hmain p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
  · have ho : (⨆ u ∈ Icc 0 T,
        eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) =
        ⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁'.a u v - S₂'.a u v) (Icc u T) := by
      apply iSup_congr
      intro u
      apply iSup_congr
      intro hu
      apply eVariationOn.eq_of_eqOn
      intro v hv
      dsimp only
      rw [e₁.a ⟨hu.1, hv.1, hv.2⟩, e₂.a ⟨hu.1, hv.1, hv.2⟩]
    have hi : (⨆ v ∈ Icc 0 T,
        eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) =
        ⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁'.b u v - S₂'.b u v) (Icc 0 v) := by
      apply iSup_congr
      intro v
      apply iSup_congr
      intro hv
      apply eVariationOn.eq_of_eqOn
      intro u hu
      dsimp only
      rw [e₁.b ⟨hu.1, hu.2, hv.2⟩, e₂.b ⟨hu.1, hu.2, hv.2⟩]
    simpa only [ho, hi] using htv

end EmcsfAcExtension.Local
