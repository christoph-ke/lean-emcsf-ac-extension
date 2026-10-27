module

public import EmcsfAcExtension.Global.Exterior.VariationTailsUniform
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceIncomingRadius

/-! # Exact terminal-radius substitution for the moving variation

The actual terminal Jacobian is `-nu(u,0)`. These identities convert the
time form of M3 to its stated radius integrals without changing any
quantitative weight. Source: `charged_SF_new_version.tex:L1368–L1379`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Exact change of variables on every proper terminal segment. The radial
integrand may be signed; no implicit constant or inverse is assumed. -/
theorem terminal_radius_integral_eq {ui e a b : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a ≤ b) (hb : b < 0)
    (g : ℝ → ℝ) :
    (∫ u in a..b, (-S.nu u 0) * g (S.r u 0)) =
      ∫ R in S.r b 0..S.r a 0, g R := by
  have hmem (u : ℝ) (hu : u ∈ Icc a b) : (u, 0) ∈ origDomain ui :=
    ⟨hia.trans hu.1, hu.2.trans_lt hb, (hu.2.trans_lt hb).le, le_rfl⟩
  have hcont : ContinuousOn (fun u => S.r u 0) (Icc a b) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hanti : StrictAntiOn (fun u => S.r u 0) (Icc a b) :=
    (Terminal.terminal_radius_strictAntiOn h.solution).mono
      (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hb⟩)
  have hchange := integral_image_eq_integral_deriv_smul_of_antitoneOn measurableSet_Ioo
    (fun u (hu : u ∈ Ioo a b) =>
      (terminal_radius_hasDerivAt h ⟨hia.trans_lt hu.1, hu.2.trans hb⟩).hasDerivWithinAt)
    (hanti.antitoneOn.mono Ioo_subset_Icc_self) g
  rw [hcont.image_Ioo_of_strictAntiOn hab hanti] at hchange
  rw [intervalIntegral.integral_of_le hab, restrict_Ioc_eq_restrict_Icc,
    ← restrict_Ioo_eq_restrict_Icc,
    intervalIntegral.integral_of_le (hanti.antitoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab),
    restrict_Ioc_eq_restrict_Icc, ← restrict_Ioo_eq_restrict_Icc]
  simpa only [smul_eq_mul] using hchange.symm

/-- [internal]
Proper moving-row continuity gives continuity on the complete existing
half-open row interval. No continuity at the missing endpoint is asserted. -/
theorem continuousOn_outgoing_variation_Ico {ui e c : ℝ} {S : Fields} {t : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : c ∈ Ioo ui 0)
    (hroot : ∀ u ∈ Ico c 0, u < t u ∧ t u < 0)
    (hm : MonotoneOn t (Ico c 0))
    (hsegments : ∀ a b, c ≤ a → a ≤ b → b < 0 →
      ∃ K L : ℝ≥0, LipschitzOnWith K t (uIcc a b) ∧
        AntilipschitzWith L ((uIcc a b).domRestrict t)) :
    ContinuousOn (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal) (Ico c 0) := by
  intro u hu
  let b := u / 2
  have hub : u < b := by dsimp [b]; linarith [hu.2]
  have hb : b < 0 := by dsimp [b]; linarith [hu.2]
  have hcb : c ≤ b := hu.1.trans hub.le
  obtain ⟨K, L, ht, ha⟩ := hsegments c b le_rfl hcb hb
  have hsub : Icc c b ⊆ Ico c 0 := fun x hx => ⟨hx.1, hx.2.trans_lt hb⟩
  have hcv := continuousOn_outgoing_variation h.solution hcb
    (by simpa only [uIcc_of_le hcb] using ht.continuousOn) (hm.mono hsub)
    (fun x hx => ⟨hc.1.le.trans hx.1, (hsub hx).2,
      (hroot x (hsub hx)).1.le, (hroot x (hsub hx)).2.le⟩)
    (fun x hx => (hroot x (hsub hx)).1)
  apply (hcv u ⟨hu.1, hub.le⟩).mono_of_mem_nhdsWithin
  apply mem_of_superset (inter_mem_nhdsWithin (Ico c 0) (Iio_mem_nhds hub))
  exact fun x hx => ⟨hx.1.1, hx.2.le⟩

/-- [internal]
Exact integrability correspondence for the same proper radius change.
It allows the separate mass and forcing radius integrals in M3 to be
split only after their individual integrability has been proved. -/
theorem terminal_radius_intervalIntegrable_iff {ui e a b : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a ≤ b) (hb : b < 0)
    (g : ℝ → ℝ) :
    IntervalIntegrable (fun u => (-S.nu u 0) * g (S.r u 0)) volume a b ↔
      IntervalIntegrable g volume (S.r b 0) (S.r a 0) := by
  have hmem (u : ℝ) (hu : u ∈ Icc a b) : (u, 0) ∈ origDomain ui :=
    ⟨hia.trans hu.1, hu.2.trans_lt hb, (hu.2.trans_lt hb).le, le_rfl⟩
  have hcont : ContinuousOn (fun u => S.r u 0) (Icc a b) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have hanti : StrictAntiOn (fun u => S.r u 0) (Icc a b) :=
    (Terminal.terminal_radius_strictAntiOn h.solution).mono
      (fun u hu => ⟨hia.trans hu.1, hu.2.trans_lt hb⟩)
  have hchange := integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
    measurableSet_Ioo
    (fun u (hu : u ∈ Ioo a b) =>
      (terminal_radius_hasDerivAt h ⟨hia.trans_lt hu.1, hu.2.trans hb⟩).hasDerivWithinAt)
    (hanti.antitoneOn.mono Ioo_subset_Icc_self) g
  rw [hcont.image_Ioo_of_strictAntiOn hab hanti] at hchange
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab,
    intervalIntegrable_iff_integrableOn_Icc_of_le
      (hanti.antitoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab),
    IntegrableOn, IntegrableOn, ← restrict_Ioo_eq_restrict_Icc,
    ← restrict_Ioo_eq_restrict_Icc]
  simpa only [IntegrableOn, smul_eq_mul] using hchange.symm

end EmcsfAcExtension.Global.Exterior
