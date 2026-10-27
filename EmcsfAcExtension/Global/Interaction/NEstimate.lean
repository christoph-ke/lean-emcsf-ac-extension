module

public import EmcsfAcExtension.Global.Interaction.NEstimateIntegrals
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
import EmcsfAcExtension.Global.Interaction.WrappersCost
import EmcsfAcExtension.Global.Interaction.PairIntegrated
import EmcsfAcExtension.Global.Interaction.ForcingRepresentative
import EmcsfAcExtension.Local.Api.Mono

/-! # Total weighted renormalized source estimate

The seven landed costs are summed on the actual finite exterior. Full
stages include their assigned connectors, without a stage-count or duration
factor. Source: `charged_SF_new_version.tex:L3599–L3608`, L3625–L3745.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem lintegral_le_sum_of_stage_bounds {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (f : ℝ → ℝ≥0∞) (A : Fin N → ℝ) (hA : ∀ n, 0 ≤ A n)
    (hbound : ∀ n, (∫⁻ u in Icc (B.cuts n.castSucc) (B.cuts n.succ), f u) ≤
      ENNReal.ofReal (A n)) :
    (∫⁻ u in Icc u₀ u₁, f u) ≤ ENNReal.ofReal (∑ n, A n) := by
  have hs := lintegral_finite_stages_le N B.cuts B.ordered f
  rw [B.first, B.last] at hs
  apply hs.trans ((Finset.sum_le_sum (fun n _ => hbound n)).trans_eq ?_)
  exact (ENNReal.ofReal_sum_of_nonneg (fun n _ => hA n)).symm

private theorem n_estimate_raw_of_profiles (δ c Λ F ε ρ Cq : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ui e u₀ u₁ v₀ R₀ M₀ : ℝ) (S : Fields) (vb g : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      IsSolution e S (origDomain ui) → u₁ ≤ 0 → 0 < R₀ → 1 ≤ M₀ →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      (∀ u ∈ Icc u₀ u₁, S.r u 0 ≤ R₀) →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb, ‖S.phi p.1 p.2‖ ≤ M₀ ∧
        |S.Q p.1 p.2| / S.r p.1 p.2 ^ 2 ≤ Cq * |e| * M₀ * F) →
      IntegrableOn g (Icc v₀ 0) →
      (∀ᵐ v ∂volume.restrict (Icc v₀ 0), 0 ≤ g v) →
      (∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v) →
      let J := ∫ v in v₀..0, g v
      let A := ∑ n, E n
      let H := ∑ n, Real.sqrt (E n)
      let ζ := Local.sigma e M₀ (2 * R₀)
      sourceInteraction e S (exteriorDomain ui u₀ u₁ vb) v₀ ≤
        ENNReal.ofReal (C * A + C * J * A + C * F * J * H +
          C * F * J ^ 2 + C * ζ * (1 + J)) := by
  rcases hbox with ⟨hδ, hδ1, hc, hcΛ, hF, hF1, hε, hgap, hρ, hρ1⟩
  have hbox : ExteriorBox δ c Λ F ε ρ :=
    ⟨hδ, hδ1, hc, hcΛ, hF, hF1, hε, hgap, hρ, hρ1⟩
  have hΛ := hc.trans_le hcΛ
  have hep : ε < 1 - F ^ 2 := (le_max_left ε (1 / 2)).trans_lt hgap
  have hε2 : ε < 2 := by linarith only [hep, sq_nonneg F]
  have h3 : 0 < 3 - F ^ 2 - ε := by linarith only [hep]
  obtain ⟨Cb, hCb, hbb⟩ := boundary_boundary_source δ c Λ F ε hδ hc hcΛ hF hF1.le h3
  obtain ⟨Cs, hCs, hsb⟩ := source_boundary_curvature δ c Λ F ε ρ hbox
  obtain ⟨Ci, hCi, hib⟩ := incoming_boundary_source δ c Λ F ε ρ hbox
  obtain ⟨Cp, hCp, hpair⟩ := pair_source_integrated δ c Λ F ε hδ hc hΛ hF hF1 hε2
  obtain ⟨Ce, hCe, hem⟩ := explicit_electromagnetic_source_cost_of_profiles_separate δ Λ F Cq
    hδ hΛ hF hCq
  obtain ⟨Cm, hCm, hmixed⟩ := electromagnetic_mixed_cost δ c Λ ε Cq hδ hc hΛ hε2 hCq
  let C := Cb + Cs + Ci + Cp + Cm + 2 * Ce + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCbC : Cb ≤ C := by dsimp [C]; linarith only [hCs, hCi, hCp, hCm, hCe]
  have hCsC : Cs ≤ C := by dsimp [C]; linarith only [hCb, hCi, hCp, hCm, hCe]
  have hCiC : Ci ≤ C := by dsimp [C]; linarith only [hCb, hCs, hCp, hCm, hCe]
  have hCpC : Cp ≤ C := by dsimp [C]; linarith only [hCb, hCs, hCi, hCm, hCe]
  have hCmC : Cm ≤ C := by dsimp [C]; linarith only [hCb, hCs, hCi, hCp, hCe]
  have hCeC : 2 * Ce ≤ C := by dsimp [C]; linarith only [hCb, hCs, hCi, hCp, hCm]
  refine ⟨C, hC, ?_⟩
  intro ui e u₀ u₁ v₀ R₀ M₀ S vb g N B E hS hu₁ hR hM hstop hupper hE hprofiles hg hg0 hmajor
  dsimp only
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hv₀ : v₀ ≤ 0 := (finite_boundary_label_bounds B u₀ ⟨le_rfl, hab⟩).1.trans
    (finite_boundary_label_bounds B u₀ ⟨le_rfl, hab⟩).2
  have ig := (intervalIntegrable_iff_integrableOn_Icc_of_le hv₀).mpr hg
  let J := ∫ v in v₀..0, g v
  let A := ∑ n, E n
  let H := ∑ n, Real.sqrt (E n)
  let ζ := Local.sigma e M₀ (2 * R₀)
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg_of_ae_restrict hv₀ hg0
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n _ => (hE n).1)
  have hH : 0 ≤ H := Finset.sum_nonneg (fun n _ => Real.sqrt_nonneg _)
  have hζ : 0 ≤ ζ := by dsimp [ζ, Local.sigma]; positivity
  have hF2 : F ^ 2 ≤ 1 := pow_le_one₀ hF hF1.le
  have hF3 : F ^ 3 ≤ 1 := pow_le_one₀ hF hF1.le
  let I := fun i : Fin 7 => ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
    ENNReal.ofReal ‖sourceContribution e S vb i u v‖
  have hb : I ⟨0, by decide⟩ ≤ ENNReal.ofReal (Cb * A) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Finset.mul_sum] using
      lintegral_le_sum_of_stage_bounds B _ (fun n => Cb * E n)
        (fun n => mul_nonneg hCb.le (hE n).1)
        (hbb e ui u₀ u₁ v₀ ρ S vb N B E hS hE hstop)
  have hs : I ⟨1, by decide⟩ ≤ ENNReal.ofReal (Cs * A * J) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Finset.mul_sum, Finset.sum_mul] using
      lintegral_le_sum_of_stage_bounds B _ (fun n => Cs * E n * J)
        (fun n => mul_nonneg (mul_nonneg hCs.le (hE n).1) hJ)
        (hsb e ui u₀ u₁ v₀ S vb g N B E hS hE hstop ig hg0 hmajor)
  have hi : I ⟨2, by decide⟩ ≤ ENNReal.ofReal (Ci * F * J * H) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Finset.mul_sum] using
      lintegral_le_sum_of_stage_bounds B _ (fun n => Ci * F * J * Real.sqrt (E n))
        (fun n => by positivity)
        (hib e ui u₀ u₁ v₀ S vb g N B E hS hE hstop ig hg0 hmajor)
  have hp : I ⟨3, by decide⟩ ≤ ENNReal.ofReal (Cp * F * J ^ 2) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ']
        using
      hpair e ui u₀ u₁ v₀ ρ S vb g N B hS hstop ig hg0 hmajor
  have hmix : I ⟨4, by decide⟩ ≤ ENNReal.ofReal (Cm * ζ * F ^ 2 * J) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ']
        using
      hmixed e ui M₀ R₀ u₀ u₁ v₀ ρ F S vb g N B hS hstop (by linarith only [hM])
        hF hR.le hupper hprofiles ig hg0 hmajor
  have hterm : inSeg u₀ u₁ 0 ⊆ exteriorDomain ui u₀ u₁ vb := by
    rintro ⟨u, v⟩ ⟨h₀, h₁, rfl⟩
    exact finite_boundary_row B u ⟨h₀, h₁⟩ ⟨rfl, (B.mem u ⟨h₀, h₁⟩).2.2.2, le_rfl⟩
  have hem' := hem e M₀ R₀ u₀ u₁ c ε S (exteriorDomain ui u₀ u₁ vb) (Icc u₀ u₁) vb
    (Local.isSolution_mono hS inter_subset_left) hstop hab hu₁ hterm measurableSet_Icc
    Subset.rfl hR.le hM (fun u hu => ⟨B.off_axis u hu, (B.mem u hu).2.2.2⟩)
    (fun u hu => finite_boundary_row B u hu) hupper
    (fun u hu v hv => (hprofiles (u, v) (finite_boundary_row B u hu ⟨rfl, hv⟩)).1)
    (fun u hu v hv => (hprofiles (u, v) (finite_boundary_row B u hu ⟨rfl, hv⟩)).2)
  have he₅ : I ⟨5, by decide⟩ ≤ ENNReal.ofReal (Ce * ζ * F ^ 3) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ']
        using hem'.2
  have he₆ : I ⟨6, by decide⟩ ≤ ENNReal.ofReal (Ce * ζ * F) := by
    simpa only [I, A, H, J, ζ, sourceContribution, Matrix.cons_val_zero', Matrix.cons_val_succ']
        using hem'.1
  have hsum : (∑ i, I i) ≤ ENNReal.ofReal
      (Cb * A + Cs * A * J + Ci * F * J * H + Cp * F * J ^ 2 + Cm * ζ * F ^ 2 * J + Ce * ζ * F ^ 3 +
          Ce * ζ * F) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    have hh := add_le_add hb (add_le_add hs (add_le_add hi
      (add_le_add hp (add_le_add hmix (add_le_add he₅ he₆)))))
    apply hh.trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    congr 1
    ring
  apply (sourceInteraction_le_sum_contributions hS B).trans (hsum.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hb' := mul_le_mul_of_nonneg_right hCbC hA
  have hs' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hA) hJ
  have hi' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCiC hF) hJ) hH
  have hp' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpC hF) (sq_nonneg J)
  have hm' := mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hF2 (mul_nonneg hCm.le hζ)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_right hCmC hζ)) hJ
  have he₅' : Ce * ζ * F ^ 3 ≤ Ce * ζ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hF3 (mul_nonneg hCe.le hζ)
  have he₆' : Ce * ζ * F ≤ Ce * ζ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hF1.le (mul_nonneg hCe.le hζ)
  have he' := mul_le_mul_of_nonneg_right hCeC hζ
  change _ ≤ C * A + C * J * A + C * F * J * H + C * F * J ^ 2 + C * ζ * (1 + J)
  linarith only [hb', hs', hi', hp', hm', he₅', he₆', he']

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.Interaction

/-- [internal]
The common-label bound on the canonical representative controls the raw
weighted derivative almost everywhere on each stopped row. The original
AC equations discharge the representative identification. No constants
or additional trace hypotheses occur. -/
theorem raw_envelope_of_representative {ui e u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb g : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), ∀ u ∈ Icc u₀ u₁,
      vb u ≤ v → ‖weightedJRepresentative e S u₀ u v‖ ≤ g v) :
    ∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc (vb u) 0),
      ‖weightedJ S u v‖ ≤ g v := by
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hia := (B.mem u₀ ⟨le_rfl, hab⟩).1
  have hraw := ae_restrict_of_ae (s := Icc v₀ 0) (ae_weighted_representation_on_orig h hia)
  intro u hu
  have hsub : Icc (vb u) 0 ⊆ Icc v₀ 0 :=
    Icc_subset_Icc (InteractionEstimate.finite_boundary_label_bounds B u hu).1 le_rfl
  filter_upwards [hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    hraw.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    ae_restrict_mem measurableSet_Icc] with v hv hr hvm
  rw [hr hvm.2 u hu.1 ((B.off_axis u hu).trans_le hvm.1)]
  exact hv u hu hvm.1

/-- [internal]
The total source estimate in the exact profile-conditional interface
requested by internal project record. `C` depends only on the fixed box and `Cq`, before
all physical data, scalar/radius scales, stage count and duration.
The production stopped-data wrapper derives both profiles; they are not
new hypotheses of the graph node. Source: `charged_SF_new_version.tex:L3599–L3608`. -/
theorem n_estimate_of_profiles (δ c Λ F ε ρ Cq : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ui e u₀ u₁ v₀ R₀ M₀ : ℝ) (S : Fields)
        (vb g : ℝ → ℝ) (N : ℕ)
        (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
      OriginalData ui e S → u₀ ≤ u₁ → u₁ < 0 → 0 < R₀ → 1 ≤ M₀ →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε →
      (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ R₀) →
      BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
      (∀ p ∈ exteriorDomain ui u₀ u₁ vb, ‖S.phi p.1 p.2‖ ≤ M₀ ∧
        |S.Q p.1 p.2| / S.r p.1 p.2 ^ 2 ≤ Cq * |e| * M₀ * F) →
      IntegrableOn g (Icc v₀ 0) →
      (∀ᵐ v ∂volume.restrict (Icc v₀ 0), 0 ≤ g v) →
      (∀ᵐ v ∂volume.restrict (Icc v₀ 0), ∀ u ∈ Icc u₀ u₁,
        vb u ≤ v → ‖weightedJRepresentative e S u₀ u v‖ ≤ g v) →
      let J := ∫ v in v₀..0, g v
      let E₁ := ∑ n, E n
      let Ehalf := ∑ n, Real.sqrt (E n)
      let ζ₂ := Local.sigma e M₀ (2 * R₀)
      sourceInteraction e S (exteriorDomain ui u₀ u₁ vb) v₀ ≤
        ENNReal.ofReal (C * E₁ + C * J * E₁ + C * F * J * Ehalf +
          C * F * J ^ 2 + C * ζ₂ * (1 + J)) := by
  obtain ⟨C, hC, hbound⟩ := InteractionEstimate.n_estimate_raw_of_profiles δ c Λ F ε ρ Cq hbox hCq
  refine ⟨C, hC, ?_⟩
  intro ui e u₀ u₁ v₀ R₀ M₀ S vb g N B E h _ hu₁ hR hM hstop hann hE hprofile hg hg0 hmajor
  exact hbound ui e u₀ u₁ v₀ R₀ M₀ S vb g N B E h.solution hu₁.le hR hM hstop
    (fun u hu => (hann u hu).2) hE hprofile hg hg0 (raw_envelope_of_representative h B hmajor)

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global.InteractionEstimate

open Interaction

/-- [node eq:ct-N-estimate]
The total weighted source bound on every sufficiently late stopped finite
exterior, including its assigned connectors. The scalar and charge
profiles are derived from the recorded hypotheses. The positive constant
depends only on `δ, c, Λ, F, ε, ρ`, before coupling, canonical `M₀`, radius,
stage count and duration; `Jstop` precedes the choice of late entry.
Source: `charged_SF_new_version.tex:L3599–L3608`, L3620–L3622. -/
theorem ct_n_estimate_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ → StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
        let J := ∫ v in v₀..0, g v
        let E₁ := ∑ n, E n
        let Ehalf := ∑ n, Real.sqrt (E n)
        let ζ₂ := Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀)
        sourceInteraction e S (exteriorDomain ui u₀ u₁ vb) v₀ ≤
          ENNReal.ofReal (C * E₁ + C * J * E₁ + C * F * J * Ehalf +
            C * F * J ^ 2 + C * ζ₂ * (1 + J)) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := n_estimate_raw_of_profiles δ c Λ F ε ρ Cq hbox hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en N B E hau d hbudget hE
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  exact hbound ui e u₀ u₁ v₀ R₀ _ S vb g N B E h.solution
    (B.mem u₁ ⟨hab, le_rfl⟩).2.1.le d.radius_pos (d.one_le_background h ⟨le_rfl, hab⟩)
    d.stops (fun u hu => (d.annulus u hu).2) hE
    (fun p hp' => (hp p.1 ⟨hp'.2.1, hp'.2.2.1⟩ p.2 ⟨hp'.2.2.2, hp'.1.2.2.2⟩).2)
    d.integrable d.nonneg
    (fun u hu => d.row_majorant hu ⟨(B.mem u hu).2.2.2, le_rfl⟩)

end EmcsfAcExtension.Global.InteractionEstimate
