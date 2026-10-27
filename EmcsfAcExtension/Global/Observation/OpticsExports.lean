module

public import EmcsfAcExtension.Global.Observation.CoreExports
public import EmcsfAcExtension.Global.Observation.Optics

/-! # Both optical directions in the source observation window

Every incoming segment point uses its own complete outgoing section.
The two normalization factors are those at the selected actual cylinder
endpoints, and all core bounds come from the source-setting core export.
Source: charged_SF_new_version.tex:L2145–2160; internal project record, co-expansions.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [node eq:co-expansions]
[node eq:co-truncated-optics]
The two original characteristic segments from the actual cylinder to
any admissible inward point satisfy the exact optical integral bounds
and both sharp normalized expansion lower bounds. Boundary normalizers,
full-section masses and charge inequalities are derived here, with no
incoming scalar supremum input. The charged threshold depends only on
`δ`, boundary constant after `δ,T`, and failure coefficient after `δ,T,ε`;
all precede physical data, scale, background, gauge and selected points. -/
theorem optics_of_failed_observation {δ : ℝ} (hδ : 0 < δ) :
    ∃ ηc : ℝ, 0 < ηc ∧
    ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / C → ∃ Cobs : ℝ, 0 < Cobs ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    0 < b → 0 < s → s ≤ b →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (∀ p ∈ triangle (γ.U (τ₀ - T * b / 2)) (γ.V (τ₀ + T * b / 2)),
      δ ≤ 1 - S.mu p.1 p.2) →
    |e| * b * (1 + ‖H‖) ≤ ηc →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal Cobs * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    ∀ α ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
    ∀ β ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2), α ≤ β →
      let u := γ.U β
      let v := γ.V α
      let cNu := (2 * (-S.nu u (γ.V β)))⁻¹
      let cLam := (2 * S.lam (γ.U α) v)⁻¹
      u < v → ∀ ρ : ℝ, 0 < ρ → s * ρ ≤ S.r u v →
      (S.m u v / s ∈ Icc 0 2 ∧ δ ≤ 1 - S.mu u v ∧
        S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) ∧
      ((0 ≤ ∫ x in (γ.U α)..u,
          -S.nu x v * (S.mu x v - S.Q x v ^ 2 / S.r x v ^ 2) /
            ((1 - S.mu x v) * S.r x v)) ∧
        (∫ x in (γ.U α)..u,
          -S.nu x v * (S.mu x v - S.Q x v ^ 2 / S.r x v ^ 2) /
            ((1 - S.mu x v) * S.r x v)) ≤ 4 / (δ * ρ)) ∧
      ((0 ≤ ∫ x in v..(γ.V β),
          S.lam u x * (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) /
            ((1 - S.mu u x) * S.r u x)) ∧
        (∫ x in v..(γ.V β),
          S.lam u x * (S.mu u x - S.Q u x ^ 2 / S.r u x ^ 2) /
            ((1 - S.mu u x) * S.r u x)) ≤ 4 / (δ * ρ)) ∧
      (((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ cNu * (-S.nu u v) ∧
          cNu * (-S.nu u v) ≤ 1 / 2) ∧
        ((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ cLam * S.lam u v ∧
          cLam * S.lam u v ≤ 1 / 2)) ∧
      (8 ≤ ρ →
        ((1 / 2 : ℝ) * Real.exp (-(8 / ρ)) ≤ cNu * (-S.nu u v) ∧
          cNu * (-S.nu u v) ≤ 1 / 2) ∧
        ((1 / 2 : ℝ) * Real.exp (-(8 / ρ)) ≤ cLam * S.lam u v ∧
          cLam * S.lam u v ≤ 1 / 2)) := by
  obtain ⟨_Ccore, _hCcore, ηc, hηc, hcore⟩ := core_bounds_of_failed_observation hδ
  refine ⟨ηc, hηc, ?_⟩
  intro T hT
  obtain ⟨C, hC, hcore⟩ := hcore T hT
  refine ⟨C, hC, ?_⟩
  intro ε hε hεC
  obtain ⟨Cobs, hCobs, hcore⟩ := hcore ε hε hεC
  refine ⟨Cobs, hCobs, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure α hα β hβ hαβ
  let u := γ.U β
  let v := γ.V α
  let cNu := (2 * (-S.nu u (γ.V β)))⁻¹
  let cLam := (2 * S.lam (γ.U α) v)⁻¹
  intro huv ρ hρ hcut
  have hclock (τ) (hτ : τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) := by
    obtain ⟨ht, heq⟩ := normalized_clock_inverse hs hτ
    have hh := hcore ui e b s τ₀ S h γ χ hb hs hsb hχ hχd hχ0 hscale hgap hcharged hfailure
      (2 * (τ - τ₀) / s) ht
    simpa only [heq] using hh
  have hclosed := hα.1.trans hα.2
  have huMono := (γ.strictMonoOn_U h.solution).monotoneOn
  have hvMono := (γ.strictMonoOn_V h.solution).monotoneOn
  have hau : γ.U α ≤ u := huMono hα hβ hαβ
  have hvb : v ≤ γ.V β := hvMono hα hβ hαβ
  have hin : inSeg (γ.U α) u v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨h1, h2, rfl⟩
    exact ⟨(γ.mem α hα).1.trans h1, (h2.trans_lt huv).trans_le (γ.mem α hα).2.2.2,
      h2.trans huv.le, (γ.mem α hα).2.2.2⟩
  have houtfull := (cylinder_full_section h.solution γ hb hβ).2
  have hout : outSeg u v (γ.V β) ⊆ origDomain ui := by
    rintro p ⟨hp, h1, h2⟩
    exact houtfull ⟨hp, huv.le.trans h1, h2⟩
  have hnormNu : cNu * (-S.nu u (γ.V β)) = 1 / 2 := by
    have hn := (h.solution.nu_neg _ (γ.mem β hβ)).ne
    dsimp only [cNu, u]
    field_simp
  have hnormLam : cLam * S.lam (γ.U α) v = 1 / 2 := by
    have hl := (h.solution.lam_pos _ (γ.mem α hα)).ne'
    dsimp only [cLam, v]
    field_simp
  have hinsection (x) (hx : x ∈ Icc (γ.U α) u) :
      ∃ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2), γ.U τ = x ∧
        x < v ∧ v ≤ γ.V τ := by
    obtain ⟨τ, hτ, heq⟩ := intermediate_value_Icc hαβ
      (γ.c1_U.continuousOn.mono (Icc_subset_Icc hα.1 hβ.2)) hx
    have hτ' : τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) :=
      ⟨hα.1.trans hτ.1, hτ.2.trans hβ.2⟩
    exact ⟨τ, hτ', heq, hx.2.trans_lt huv, hvMono hα hτ' hτ.1⟩
  have hmi (x) (hx : x ∈ Icc (γ.U α) u) : S.m x v ≤ 2 * s := by
    obtain ⟨τ, hτ, heq, h1, h2⟩ := hinsection x hx
    have hh := ((hclock τ hτ).1 v ⟨by simpa only [heq] using h1.le, h2⟩).2
    rw [heq] at hh
    exact (div_le_iff₀ hs).mp hh
  have hmo (x) (hx : x ∈ Icc v (γ.V β)) : S.m u x ≤ 2 * s :=
    (div_le_iff₀ hs).mp (((hclock β hβ).1 x ⟨huv.le.trans hx.1, hx.2⟩).2)
  have hgi (x) (hx : x ∈ Icc (γ.U α) u) : δ ≤ 1 - S.mu x v := by
    obtain ⟨τ, hτ, heq, h1, h2⟩ := hinsection x hx
    have hh := cylinder_full_section_subset_triangle h.solution γ hτ
      (show (γ.U τ, v) ∈ outSeg (γ.U τ) (γ.U τ) (γ.V τ) from
        ⟨rfl, by simpa only [heq] using h1.le, h2⟩)
    simpa only [heq] using hgap _ hh
  have hgo (x) (hx : x ∈ Icc v (γ.V β)) : δ ≤ 1 - S.mu u x :=
    hgap (u, x) (cylinder_full_section_subset_triangle h.solution γ hβ
      (show (u, x) ∈ outSeg u u (γ.V β) from ⟨rfl, huv.le.trans hx.1, hx.2⟩))
  have hqi (x) (hx : x ∈ Icc (γ.U α) u) : S.Q x v ^ 2 / S.r x v ^ 2 ≤ S.mu x v := by
    obtain ⟨τ, hτ, heq, h1, h2⟩ := hinsection x hx
    have hh := ((hclock τ hτ).2.2 v ⟨by simpa only [heq] using h1, h2⟩).2.2.2.1
    rw [heq] at hh
    have hh' := (le_div_iff₀ (hδ.trans_le (hgi x hx))).mp hh
    linarith only [hh']
  have hqo (x) (hx : x ∈ Icc v (γ.V β)) : S.Q u x ^ 2 / S.r u x ^ 2 ≤ S.mu u x := by
    have hh := ((hclock β hβ).2.2 x ⟨huv.trans_le hx.1, hx.2⟩).2.2.2.1
    have hh' := (le_div_iff₀ (hδ.trans_le (hgo x hx))).mp hh
    linarith only [hh']
  exact ⟨⟨(hclock β hβ).1 v ⟨huv.le, hvb⟩, hgo v ⟨le_rfl, hvb⟩,
      hqo v ⟨le_rfl, hvb⟩⟩, incoming_truncated_optics_of_mass_charge_bounds h.solution hδ hρ hs
      hau huv hin hcut hmi hgi hqi,
    outgoing_truncated_optics_of_mass_charge_bounds h.solution hδ hρ hs
      huv hvb hout hcut hmo hgo hqo,
    co_expansions_of_original_segments h.solution hδ hρ hs hau huv hvb hin hout hcut
      hmi hmo hgi hgo hqi hqo hnormNu hnormLam,
    fun hρ8 => co_expansions_outer_of_original_segments h.solution hρ8 hs
      hau huv hvb hin hout hcut
      hmi hmo hqi hqo hnormNu hnormLam⟩

end EmcsfAcExtension.Global.Observation
