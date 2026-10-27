module

public import EmcsfAcExtension.Global.Exterior.VariationTailsRadialModulus
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcingExplicit

/-! # The literal radius-integral moving-interval inequality

The radial variation profile is the actual moving-row variation composed
with the canonical terminal-radius inverse. Both proper radius integrals
and the universal coefficients remain explicit. Source:
`charged_SF_new_version.tex:L1368–L1379`, approved internal project record (M3).
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
M3 with its literal radius integrals. The continuous radial profile `VR`
is identified with the actual outgoing variation on every late row.
The common coefficient `20744` is universal; the entry row and
profile depend on the fixed original data, coupling and adaptive profile,
uniformly in both proper endpoints. Every source and variation bound used
to construct the profile is proved from the terminal inputs. -/
theorem moving_interval_modulus_inequality_radial_of_terminal
    {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ c ∈ Ioo ui 0, ∃ t VR : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      ContinuousOn VR (Ioc 0 (S.r c 0)) ∧
      (∀ u ∈ Ico c 0, VR (S.r u 0) =
        (eVariationOn (S.a u) (Icc (t u) 0)).toReal) ∧
      ∀ a b, c ≤ a → a ≤ b → b < 0 →
        (eVariationOn (S.a b) (Icc (t b) 0)).toReal +
          (∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
        (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
          20744 * (∫ R in S.r b 0..S.r a 0, (M R / ell R ^ 2) * VR R) +
          20744 * (∫ R in S.r b 0..S.r a 0, exteriorForcing e M ell
            (fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))) R) := by
  obtain ⟨c, hc, t, k, q, hroot, hmono, htt, hsegments, hk, hq, hpos,
      hopt, hhistory, hsource, hk_eq, hq_eq⟩ :=
    terminal_derivative_forcing_setup_explicit h M ell hR hC hk₀ hLip hMc hM hAfinite
      hcollapse hmass hell hellsmall hsmall hphi
  let V := fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal
  have hproper (u : ℝ) (hu : u ∈ Ico c 0) : u < t u ∧ t u < 0 :=
    ⟨(hroot u hu).1, (hroot u hu).2.1⟩
  have cV : ContinuousOn V (Ico c 0) :=
    continuousOn_outgoing_variation_Ico h hc hproper hmono.monotoneOn hsegments
  have hbound := outgoing_variation_bound_of_history h hc hproper hmono.monotoneOn
    hsegments hk hq (fun u hu => (hpos u hu).1) (fun u hu => (hpos u hu).2) hhistory
  have hmem (u : ℝ) (hu : u ∈ Ico c 0) : (u, 0) ∈ origDomain ui :=
    ⟨hc.1.le.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have cR : ContinuousOn (fun u => S.r u 0) (Ico c 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hmem
  have aR : StrictAntiOn (fun u => S.r u 0) (Ico c 0) :=
    (Terminal.terminal_radius_strictAntiOn h.solution).mono
      (fun u hu => ⟨hc.1.le.trans hu.1, hu.2⟩)
  obtain ⟨VR, cVR, hVR, hVRbound⟩ := radial_profile_of_terminal_order hc.2 cR aR
    (fun u hu => h.solution.r_pos (u, 0) (hmem u hu) hu.2) hcollapse cV
    (fun u hu => ⟨ENNReal.toReal_nonneg, hbound u hu⟩)
  refine ⟨c, hc, t, VR, hroot, cVR, hVR, ?_⟩
  intro a b ha hab hb
  obtain ⟨K, L, ht, hat⟩ := hsegments a b ha hab hb
  have hlate (u : ℝ) (hu : u ∈ Icc a b) : u ∈ Ico c 0 :=
    ⟨ha.trans hu.1, hu.2.trans_lt hb⟩
  have hsub : uIcc a b ⊆ uIcc c 0 := by
    rw [uIcc_of_le hab, uIcc_of_le hc.2.le]
    exact Icc_subset_Icc ha hb.le
  have hm : MonotoneOn t (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact hmono.monotoneOn.mono (fun u hu => hlate u hu)
  have he := moving_interval_modulus_inequality_of_history_bound h.solution hab ht hm hat
    (fun u hu => ⟨hc.1.le.trans (hlate u hu).1, (hlate u hu).2,
      (hroot u (hlate u hu)).1.le, (hroot u (hlate u hu)).2.1.le⟩)
    (fun u hu => (hroot u (hlate u hu)).1) (hk.mono_set hsub) (hq.mono_set hsub)
    (fun u hu => hhistory a u (hc.1.le.trans ha) hu.1 (hlate u hu))
  let G := exteriorForcing e M ell
    (fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R))))
  let AV := fun R => (M R / ell R ^ 2) * VR R
  have ikV : IntervalIntegrable (fun u => k u * V u) volume a b :=
    (hk.mono_set hsub).mul_continuousOn (by
      rw [uIcc_of_le hab]
      exact cV.mono (fun u hu => hlate u hu))
  have iAT : IntervalIntegrable (fun u => (-S.nu u 0) * AV (S.r u 0)) volume a b := by
    apply (ikV.const_mul (1 / 20744 : ℝ)).congr
    intro u hu
    rw [uIoc_of_le hab] at hu
    dsimp only [AV]
    rw [hVR u (hlate u ⟨hu.1.le, hu.2⟩), hk_eq]
    dsimp only [V]
    ring
  have iGT : IntervalIntegrable (fun u => (-S.nu u 0) * G (S.r u 0)) volume a b := by
    apply ((hq.mono_set hsub).const_mul (1 / 20480 : ℝ)).congr
    intro u _hu
    rw [hq_eq]
    dsimp only [G]
    ring
  have iAR := (terminal_radius_intervalIntegrable_iff h (hc.1.le.trans ha) hab hb AV).1 iAT
  have iGR := (terminal_radius_intervalIntegrable_iff h (hc.1.le.trans ha) hab hb G).1 iGT
  have hAV := terminal_radius_integral_eq h (hc.1.le.trans ha) hab hb AV
  have hG := terminal_radius_integral_eq h (hc.1.le.trans ha) hab hb G
  have hexact : (∫ u in a..b, (k u * V u + q u)) =
      20744 * (∫ R in S.r b 0..S.r a 0, AV R) +
        20480 * (∫ R in S.r b 0..S.r a 0, G R) := by
    calc
      _ = ∫ u in a..b, (20744 * ((-S.nu u 0) * AV (S.r u 0)) +
          20480 * ((-S.nu u 0) * G (S.r u 0))) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hab] at hu
        dsimp only [AV, G]
        rw [hVR u (hlate u hu), hk_eq, hq_eq]
        dsimp only [V]
        ring
      _ = 20744 * (∫ u in a..b, (-S.nu u 0) * AV (S.r u 0)) +
          20480 * (∫ u in a..b, (-S.nu u 0) * G (S.r u 0)) := by
        rw [intervalIntegral.integral_add (iAT.const_mul 20744) (iGT.const_mul 20480),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [hAV, hG]
  change V b + _ ≤ V a + _ at he
  rw [hexact] at he
  have hGnonneg : 0 ≤ ∫ R in S.r b 0..S.r a 0, G R := by
    rw [← hG]
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have hqnonneg := (hpos u (hlate u hu)).2
    rw [hq_eq] at hqnonneg
    change 0 ≤ 20480 * (-S.nu u 0) * G (S.r u 0) at hqnonneg
    nlinarith only [hqnonneg]
  have hfinal : V b + (∫ u in a..b,
        deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
      V a + 20744 * (∫ R in S.r b 0..S.r a 0, AV R) +
        20744 * (∫ R in S.r b 0..S.r a 0, G R) := by
    linarith only [he, hGnonneg]
  simpa only [V, AV, G] using hfinal

end EmcsfAcExtension.Global.Exterior
