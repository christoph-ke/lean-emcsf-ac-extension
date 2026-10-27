module

public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcingTerminal
public import EmcsfAcExtension.Global.Exterior.VariationTailsRadius
public import EmcsfAcExtension.Infra.Level.OrderIso
public import EmcsfAcExtension.Global.Terminal.OpticalUpper

/-! # Radius profiles and exact incoming-radius majorants

The actual time-row supremum is transported by the canonical decreasing
terminal-radius order isomorphism. The incoming Jacobian is kept literally
as `-nu`; no endpoint lower bound is assumed. Source:
`charged_SF_new_version.tex:L1356–L1360`, L1405–L1408; internal project record (I1)–(I2).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
A continuous time profile has a continuous radial representative under a
strictly decreasing positive terminal radius collapsing to zero. Bounds
are preserved exactly, with coefficient `1`. No inverse is assumed. -/
theorem radial_profile_of_terminal_order {c B : ℝ} {R sf : ℝ → ℝ}
    (hc : c < 0) (hR : ContinuousOn R (Ico c 0))
    (hanti : StrictAntiOn R (Ico c 0)) (hpos : ∀ u ∈ Ico c 0, 0 < R u)
    (ht : Tendsto R (𝓝[<] 0) (𝓝 0)) (hsf : ContinuousOn sf (Ico c 0))
    (hb : ∀ u ∈ Ico c 0, 0 ≤ sf u ∧ sf u ≤ B) :
    ∃ SF : ℝ → ℝ, ContinuousOn SF (Ioc 0 (R c)) ∧
      (∀ u ∈ Ico c 0, SF (R u) = sf u) ∧
      (∀ r ∈ Ioc 0 (R c), 0 ≤ SF r ∧ SF r ≤ B) := by
  let E := Level.terminalOrderIso hc hR hanti hpos ht
  let SF : ℝ → ℝ := fun r => if hr : r ∈ Ioc 0 (R c) then
    sf ((E.symm ⟨r, hr⟩).ofDual : ℝ) else 0
  have csub : Continuous (fun r : Ioc 0 (R c) => sf ((E.symm r).ofDual : ℝ)) :=
    hsf.domRestrict.comp E.symm.continuous
  have cSF : ContinuousOn SF (Ioc 0 (R c)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert csub using 1
    funext r
    change SF r = _
    dsimp only [SF]
    rw [dite_eq_left r.property]
  refine ⟨SF, cSF, ?_, ?_⟩
  · intro u hu
    have hr : R u ∈ Ioc 0 (R c) :=
      ⟨hpos u hu, hanti.antitoneOn ⟨le_rfl, hc⟩ hu hu.1⟩
    have he : E (OrderDual.toDual (⟨u, hu⟩ : Ico c 0)) = ⟨R u, hr⟩ := by
      apply Subtype.ext
      exact Level.terminalOrderIso_apply hc hR hanti hpos ht _
    dsimp only [SF]
    rw [dite_eq_left hr, ← he, E.symm_apply_apply]
    rfl
  · intro r hr
    dsimp only [SF]
    rw [dite_eq_left hr]
    exact hb _ (E.symm ⟨r, hr⟩).ofDual.property

/-- [internal]
Every nonnegative radial majorant controls incoming proper-time integrals
by its actual radius tail. The coefficient `K` is fixed before both
endpoints; no carrier or final-time dependence is introduced. -/
theorem incoming_integral_le_radius_tail {ui e c a b K : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hc : c ∈ Ico ui 0)
    (hca : c ≤ a) (hab : a ≤ b) (hb : b < 0) (hK : 0 ≤ K)
    {T f : ℝ → ℝ} (hT : IntegrableOn T (Ioc 0 (S.r c 0)))
    (hT0 : ∀ r ∈ Ioc 0 (S.r c 0), 0 ≤ T r)
    (hf : IntervalIntegrable f volume a b)
    (hfT : ∀ u ∈ Icc a b, f u ≤ K * ((-S.nu u 0) * T (S.r u 0))) :
    (∫ u in a..b, f u) ≤ K * ∫ r in Ioc 0 (S.r a 0), T r := by
  have hmem (u : ℝ) (hu : u ∈ Ico c 0) : (u, 0) ∈ origDomain ui :=
    ⟨hc.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have hanti := (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
  have hRa : S.r a 0 ≤ S.r c 0 := hanti hc ⟨hc.1.trans hca, hab.trans_lt hb⟩ hca
  have htail : Ioc 0 (S.r a 0) ⊆ Ioc 0 (S.r c 0) := Ioc_subset_Ioc_right hRa
  have htime := integrable_terminal_radius_pullback h hc le_rfl hT
  have htimeab : IntervalIntegrable (fun u => (-S.nu u 0) * T (S.r u 0)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      (htime.mono_set (fun u hu => ⟨hca.trans hu.1, hu.2.trans_lt hb⟩))
  have hchange := integral_image_eq_integral_deriv_smul_of_antitoneOn measurableSet_Ioo
    (fun u (hu : u ∈ Ioo a b) =>
      (terminal_radius_hasDerivAt h
        ⟨hc.1.trans_lt (hca.trans_lt hu.1), hu.2.trans hb⟩).hasDerivWithinAt)
    (hanti.mono (fun u hu => ⟨hc.1.trans (hca.trans hu.1.le), hu.2.trans hb⟩)) T
  have himage : (fun u => S.r u 0) '' Ioo a b ⊆ Ioc 0 (S.r a 0) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨h.solution.r_pos (u, 0) (hmem u ⟨hca.trans hu.1.le, hu.2.trans hb⟩)
      (hu.2.trans hb), hanti ⟨hc.1.trans hca, hab.trans_lt hb⟩
        ⟨hc.1.trans (hca.trans hu.1.le), hu.2.trans hb⟩ hu.1.le⟩
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 (S.r a 0))] T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hT0 r (htail hr)
  have hsub := setIntegral_mono_set (hT.mono_set htail) hnonneg
    (ae_of_all volume (fun r hr => himage hr))
  have htailbound : (∫ u in a..b, (-S.nu u 0) * T (S.r u 0)) ≤
      ∫ r in Ioc 0 (S.r a 0), T r := by
    rw [intervalIntegral.integral_of_le hab, restrict_Ioc_eq_restrict_Icc,
      ← restrict_Ioo_eq_restrict_Icc]
    simpa only [smul_eq_mul] using hchange.symm.trans_le hsub
  calc
    _ ≤ ∫ u in a..b, K * ((-S.nu u 0) * T (S.r u 0)) :=
      intervalIntegral.integral_mono_on hab hf (htimeab.const_mul K) hfT
    _ = K * ∫ u in a..b, (-S.nu u 0) * T (S.r u 0) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htailbound hK

end EmcsfAcExtension.Global.Exterior
