module

public import EmcsfAcExtension.Global.Exterior.OpticsSpeed

/-! # Pullback of radial forcing to incoming time

The Jacobian is the actual negative incoming expansion on the terminal
cone. This is the substitution used in M3–M5 and D2 of approved internal project record,
`charged_SF_new_version.tex:L1364–L1416`. No positive lower bound for the Jacobian is
assumed at the missing endpoint. No implicit constant occurs.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Every radial L¹ majorant pulls back to an L¹ incoming-time majorant with
the literal terminal-radius Jacobian. The statement permits a signed
majorant, and so does not need a separate measurable representative or
an a.e. pullback argument. -/
theorem integrable_terminal_radius_pullback {ui e c R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hc : c ∈ Ico ui 0) (hRc : S.r c 0 ≤ R₀)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc 0 R₀)) :
    IntegrableOn (fun u => (-S.nu u 0) * g (S.r u 0)) (Ico c 0) := by
  have hmem (u : ℝ) (hu : u ∈ Ico c 0) : (u, 0) ∈ origDomain ui :=
    ⟨hc.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have hR : ContinuousOn (fun u => S.r u 0) (Ico c 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hanti : StrictAntiOn (fun u => S.r u 0) (Ico c 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico c 0) hR
    intro u hu
    rw [interior_Ico] at hu
    have hd := terminal_radius_hasDerivAt h ⟨hc.1.trans_lt hu.1, hu.2⟩
    rw [hd.deriv]
    exact h.solution.nu_neg (u, 0) (hmem u ⟨hu.1.le, hu.2⟩)
  have himage : (fun u => S.r u 0) '' Ioo c 0 ⊆ Ioc 0 R₀ := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨h.solution.r_pos (u, 0) (hmem u ⟨hu.1.le, hu.2⟩) hu.2,
      (hanti.antitoneOn ⟨le_rfl, hc.2⟩ ⟨hu.1.le, hu.2⟩ hu.1.le).trans hRc⟩
  have hchange := integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    measurableSet_Ioo
    (fun u hu => (terminal_radius_hasDerivAt h ⟨hc.1.trans_lt hu.1, hu.2⟩).hasDerivWithinAt)
    (hanti.antitoneOn.mono Ioo_subset_Ico_self) g
  apply (integrableOn_Ico_iff_integrableOn_Ioo (by finiteness)).mpr
  simpa only [smul_eq_mul] using hchange.mp (hg.mono_set himage)

end EmcsfAcExtension.Global.Exterior
