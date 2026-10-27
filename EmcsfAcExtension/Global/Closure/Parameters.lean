module

public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Cooling.ObservationInput
import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Global.Interaction.ConnectorBudget
import EmcsfAcExtension.Global.Closure.Continuation

/-! # Order of the fixed stopping parameters

Numerical choices at charged_SF_new_version.tex:L3854–L3871 and in approved internal project record.
Observation thresholds precede weak stops and contraction choices. The actual
cooling and connector laws then provide the fixed recurrence coefficients
before every physical entry row; only observation remains an explicit input.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [def-node eq:cc-stop]
All weak stops at a finite cutoff of the actual boundary path,
charged_SF_new_version.tex:L3936–L3945. `J` and `Svar` are the accumulated incoming
interaction and cylinder variation. The field box is only one component;
the terminal radius and accumulated budget have their own stops. -/
@[expose] def FiniteCutoffStops (S : Fields) (ui u₀ R₀ : ℝ) (vb J Svar : ℝ → ℝ)
    (δ c Λ F ε εstop t : ℝ) : Prop :=
  ExteriorStops S (exteriorDomain ui u₀ t vb) δ c Λ F ε ∧
    (∀ u ∈ Set.Icc u₀ t, R₀ / 2 ≤ S.r u 0) ∧ J t + Svar t ≤ εstop

/-- [internal] The strict version of the five source stops. The independent
gap, charge and global expansion upper bounds remain weak components. -/
@[expose] def StrictFiniteCutoffStops (S : Fields) (ui u₀ R₀ : ℝ) (vb J Svar : ℝ → ℝ)
    (δ c Λ F ε εstop t : ℝ) : Prop :=
  ExteriorStops S (exteriorDomain ui u₀ t vb) δ c Λ F ε ∧
    (∀ p ∈ exteriorDomain ui u₀ t vb,
      c < S.lam p.1 p.2 ∧
      ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ < F ∧
      S.mu p.1 p.2 / (1 - S.mu p.1 p.2) < ε) ∧
    (∀ u ∈ Set.Icc u₀ t, R₀ / 2 < S.r u 0) ∧ J t + Svar t < εstop

/-- [internal] Continuity interface for the full finite-cutoff stops.
The five residuals are the cumulative expansion, radius, scalar, mass and
budget stops on one available proper path. The consumer proves their
continuity and literal weak/strict characterizations from finite-cutoff
continuity; strict improvement then precedes any stage continuation. -/
theorem finite_stopping_continuation_of_estimates {S : Fields} {ui u₀ R₀ T : ℝ}
    {vb J Svar : ℝ → ℝ} {δ c Λ F ε εstop : ℝ} (hT : u₀ ≤ T)
    (f : Fin 5 → ℝ → ℝ) (hf : ∀ i, ContinuousOn (f i) (Set.Icc u₀ T))
    (hweak : ∀ t ∈ Set.Icc u₀ T,
      FiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop t ↔ ∀ i, f i t ≤ 0)
    (hstrict : ∀ t ∈ Set.Icc u₀ T,
      StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop t ↔ ∀ i, f i t < 0)
    (hentry : StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop u₀)
    (himprove : ∀ t ∈ Set.Icc u₀ T,
      FiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop t →
      StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop t) :
    ∀ t ∈ Set.Icc u₀ T,
      StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop t := by
  have hres := finite_stops_of_estimates hf
    ((hstrict u₀ ⟨le_rfl, hT⟩).mp hentry) (by
      intro t ht hft
      exact (hstrict t ht).mp (himprove t ht ((hweak t ht).mpr hft)))
  intro t ht
  exact (hstrict t ht).mpr (hres t ht)

/-- [internal] Choose positive weak scalar and mass thresholds below both
supplied observation/cooling thresholds. All inputs are fixed geometric
constants, before any entry row, energy, radius, stage count or duration.
The late exterior expansion margin is not asserted by this numerical lemma. -/
theorem exists_weak_stopping_bounds (δ c Λ ηobs ηcool : ℝ)
    (hδ : 0 < δ ∧ δ ≤ 1) (hc : 0 < c) (hcΛ : c ≤ Λ)
    (ho : 0 < ηobs) (hh : 0 < ηcool) :
    ∃ F ε : ℝ, 0 < F ∧ 0 < ε ∧ F + ε < ηobs ∧ F + ε < ηcool ∧
      ∀ ρ : ℝ, 0 < ρ ∧ ρ < 1 → ExteriorBox δ c Λ F ε ρ := by
  let t := min (1 / 4 : ℝ) (min ηobs ηcool / 4)
  have ht : 0 < t := lt_min (by norm_num) (div_pos (lt_min ho hh) (by norm_num))
  have htq : t ≤ 1 / 4 := min_le_left _ _
  have hto : t ≤ ηobs / 4 :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hth : t ≤ ηcool / 4 :=
    (min_le_right _ _).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have htsq : t ^ 2 ≤ t := by
    have hm := mul_le_mul_of_nonneg_left (show t ≤ 1 by linarith only [htq]) ht.le
    simpa only [mul_one, pow_two] using hm
  refine ⟨t, t, ht, ht, by linarith only [hto, ho], by linarith only [hth, hh], ?_⟩
  intro ρ hρ
  exact ⟨hδ.1, hδ.2, hc, hcΛ, ht.le, by linarith only [htq], ht.le,
    max_lt (by linarith only [htq, htsq]) (by linarith only [htq, htsq]), hρ.1, hρ.2⟩

/-- [internal]
Fix weak bounds before the connector ratio and every shrinking scale.
They lie strictly below both supplied observation and cooling thresholds,
and the stopped mass quotient and scalar bound imply those thresholds.
All constants depend only on the fixed geometric box and thresholds,
uniformly in the solution, coupling, entry row and stage.
Source: charged_SF_new_version.tex:L3854–L3860. -/
theorem weak_stopping_parameters (δ c Λ ηobs ηcool : ℝ)
    (hδ : 0 < δ ∧ δ ≤ 1) (hc : 0 < c) (hcΛ : c ≤ Λ)
    (ho : 0 < ηobs) (hh : 0 < ηcool) :
    ∃ F ε : ℝ, 0 < F ∧ 0 < ε ∧
      (∀ ρ : ℝ, 0 < ρ ∧ ρ < 1 → ExteriorBox δ c Λ F ε ρ) ∧
      ∀ μ x : ℝ, 0 ≤ μ → μ < 1 → μ / (1 - μ) ≤ ε →
        x ≤ F → μ + x < ηobs ∧ μ + x < ηcool := by
  obtain ⟨F, ε, hF, hε, hFo, hFh, hbox⟩ :=
    exists_weak_stopping_bounds δ c Λ ηobs ηcool hδ hc hcΛ ho hh
  refine ⟨F, ε, hF, hε, hbox, ?_⟩
  intro μ x hμ hμ1 hquot hx
  have hμle : μ ≤ μ / (1 - μ) := by
    apply (le_div_iff₀ (sub_pos.mpr hμ1)).mpr
    nlinarith only [sq_nonneg μ]
  have hsum : μ + x ≤ ε + F := add_le_add (hμle.trans hquot) hx
  constructor <;> linarith only [hsum, hFo, hFh]

/-- [internal] The cooling fraction is chosen after the fixed connector and
energy-equivalence factor `K`, and before entry parameters. The coefficient
depends only on `χ` and `K`, uniformly in every physical scale and stage. -/
theorem exists_cooling_fraction (χ K : ℝ) (hχ : 0 < χ) (hK : 0 < K) :
    ∃ d : ℝ, 0 < d ∧ K * d < χ := by
  refine ⟨χ / (2 * K), div_pos hχ (by positivity), ?_⟩
  have heq : K * (χ / (2 * K)) = χ / 2 := by field_simp
  rw [heq]
  linarith only [hχ]

/-- [internal] The simultaneous entry choice's numerical clock margin,
internal project record (E1). The fixed coefficients `H`, `ρ`, `χ` precede entry data;
`εentry` is fixed before the shrinking radii `b₀`, `R₀` are selected.
No existence of physical stages is used in imposing this entry condition. -/
theorem clock_loss_lt_of_entry_ratio {H ρ χ εentry b₀ R₀ : ℝ}
    (hH : 0 ≤ H) (hρ : 0 < ρ ∧ ρ < χ) (he : 0 < εentry ∧ εentry ≤ 1)
    (hb : 0 ≤ b₀) (hR : 0 < R₀)
    (hratio : b₀ / (εentry * R₀) < 1 / (16 * (H / (1 - ρ / χ) + 1))) :
    2 * (H * b₀ / (εentry * (1 - ρ / χ)) + b₀) < R₀ / 4 := by
  have hχ : 0 < χ := hρ.1.trans hρ.2
  have hg : 0 < 1 - ρ / χ := sub_pos.mpr ((div_lt_one hχ).mpr hρ.2)
  let A := H / (1 - ρ / χ) + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hq := mul_lt_mul_of_pos_left hratio (mul_pos hA hR)
  have hleft : A * R₀ * (b₀ / (εentry * R₀)) = A * (b₀ / εentry) := by
    field_simp [he.1.ne', hR.ne']
  have hright : A * R₀ * (1 / (16 * A)) = R₀ / 16 := by
    field_simp [hA.ne']
  change A * R₀ * (b₀ / (εentry * R₀)) < A * R₀ * (1 / (16 * A)) at hq
  rw [hleft, hright] at hq
  have hbe : b₀ ≤ b₀ / εentry := (le_div_iff₀ he.1).mpr
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he.2 hb)
  have heq : H * b₀ / (εentry * (1 - ρ / χ)) = (A - 1) * (b₀ / εentry) := by
    dsimp [A]
    field_simp [he.1.ne', hg.ne']
    ring
  rw [heq]
  nlinarith only [hq, hbe, hR]

/-- [internal] The actual cylinder energy controls the pointwise norm used
by `BoundaryBudgets`. The coefficient `2` is universal, before the fields,
radius and labels. This algebraic comparison does not supply an integrated
cooling estimate or a connector budget. -/
theorem cylinder_energy_controls_boundary_norm (S : Fields) (b u v : ℝ)
    (hb : 0 < b) (hmu : 0 ≤ S.mu u v ∧ S.mu u v < 1) :
    0 ≤ cylinderEnergy S b u v / b ∧
      S.m u v / S.r u v + ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 ≤
        2 * (cylinderEnergy S b u v / b) := by
  have hg : 0 < 1 - S.mu u v := sub_pos.mpr hmu.2
  have hlog := Real.log_le_sub_one_of_pos hg
  have heq : cylinderEnergy S b u v / b =
      (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 - Real.log (1 - S.mu u v)) / 2 := by
    unfold cylinderEnergy
    field_simp [hb.ne']
  have hm : S.m u v / S.r u v = S.mu u v / 2 := by
    unfold Fields.mu
    ring
  rw [heq, hm]
  constructor <;> nlinarith only [hlog, hmu.1, sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖]

/-- [internal] The first prescribed radius is the adaptive entry radius. -/
@[simp] theorem stageRadius_zero (ρ b₀ : ℝ) : stageRadius ρ b₀ 0 = b₀ := by
  simp [stageRadius]

/-- [internal] Consecutive prescribed radii have the fixed connector ratio. -/
theorem stageRadius_succ (ρ b₀ : ℝ) (n : ℕ) :
    stageRadius ρ b₀ (n + 1) = ρ * stageRadius ρ b₀ n := by
  simp only [stageRadius, pow_succ]
  ring

/-- [internal] Every finite prescribed radius is positive. -/
theorem stageRadius_pos {ρ b₀ : ℝ} (hρ : 0 < ρ) (hb : 0 < b₀) (n : ℕ) :
    0 < stageRadius ρ b₀ n := mul_pos (pow_pos hρ n) hb

end EmcsfAcExtension.Global.Closure

namespace EmcsfAcExtension.Global

/-- [internal] The source recurrence from actual cooling and connector
propositions. The sole pending proposition is the literal architecture
observation input; cooling is discharged by its landed full theorem.
The window and weak/charged thresholds depend only on the fixed gap and
observation, before `εweak,ρ,χ`. The remaining coefficients depend only on
those fixed choices, before all physical data.
The connector may be truncated; every error multiplies the preceding
cooled energy, and there is no electromagnetic energy floor.
Source: charged_SF_new_version.tex:L3862–L3871, L3908–L3917. -/
theorem cc_recurrence_of_estimates (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
    (hobs : Cooling.observationInput δ) :
    ∃ Tstar δstar ηstar : ℝ, 0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → 0 < χ →
      ∃ K d H Cd C₁ : ℝ, 0 < K ∧ 0 < d ∧ 0 < H ∧ 0 < Cd ∧ 0 < C₁ ∧ 2 * K * d < χ ∧
      ∀ (c Λ F ui e b ε x Bterm Jstop R₀ : ℝ) (S : Fields) (g : ℝ → ℝ),
      0 < c → 0 ≤ F → F < 1 → 0 < b → 0 < ε → 0 ≤ Jstop → b ≤ R₀ →
      OriginalData ui e S →
      ∀ γ : ClockCylinder S (origDomain ui) b 0 (H * b / ε),
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 (H * b / ε) →
      (∀ τ ∈ Set.Icc 0 (H * b / ε), S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
      (∀ τ ∈ Set.Icc (Tstar * b) (H * b / ε - Tstar * b),
        triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
        (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
      cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε →
      let a := γ.U (H * b / ε)
      let v := γ.V (H * b / ε)
      a ≤ x → x < v →
      (∀ u ∈ Set.Icc a x, ρ * b ≤ S.r u v) →
      ExteriorStops S (exteriorDomain ui a x (fun _ => v)) δ c Λ F εweak →
      (∀ u ∈ Set.Icc a x, ∀ w ∈ Set.Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Set.Icc a x, ‖S.phi u 0‖ ≤ Bterm) →
      IntegrableOn g (Set.Icc v 0) →
      (∀ᵐ w ∂volume.restrict (Set.Icc v 0), 0 ≤ g w) →
      (∀ u ∈ Set.Icc a x, ∀ᵐ w ∂volume.restrict (Set.Icc v 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v..0, g w) ≤ Jstop →
      e ^ 2 * (1 + Bterm + (F + c⁻¹ * Jstop) / (1 - F ^ 2)) ^ 2 * R₀ ^ 2 ≤ 1 →
      let σ := (curveCovVar e S S.a γ.U γ.V 0 (H * b / ε)).toReal
      cylinderEnergy S (S.r x v) x v / S.r x v ≤ χ * ε + C₁ * σ ^ 2 := by
  obtain ⟨Ts, δs, ηs, _, hTs, hδs, hηs, _, hcooling⟩ :=
    charged_cool_full_of_observation δ hδ hobs
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨K, hK, hconnect⟩ := Interaction.connector_budget δ ρ εweak hδ.1 hδ.2.le hρ hεweak
  obtain ⟨d, hd, hcontract⟩ := Closure.exists_cooling_fraction χ (2 * K) hχ (by positivity)
  obtain ⟨H, Cd, hH, hCd, hcool⟩ := hcooling d hd
  let C₁ := 1 + 2 * K * Cd
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  refine ⟨K, d, H, Cd, C₁, hK, hd, hH, hCd, hC₁, hcontract, ?_⟩
  intro c Λ F ui e b ε x Bterm Jstop R₀ S g hc hF hF1 hb he hJ hbR h γ hac
    hweak hwindows hentry
  dsimp only
  intro hax hxv hrange hstop hcore hterm hg hg0 hmajor hJg hscale
  have hT : 0 < H * b / ε := by positivity
  have hcooled := (hcool ui e b ε (H * b / ε) S hb he hT h γ hac
    hweak hwindows).2 hentry rfl
  let σ := (curveCovVar e S S.a γ.U γ.V 0 (H * b / ε)).toReal
  let E := 2 * (d * ε + Cd * σ ^ 2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hp := γ.mem _ (right_mem_Icc.mpr hT.le)
  have hrad := γ.radius _ (right_mem_Icc.mpr hT.le)
  have hinit := (Closure.cylinder_energy_controls_boundary_norm S b
    (γ.U (H * b / ε)) (γ.V (H * b / ε)) hb (h.mu _ hp)).2
  have hbudget : S.m (γ.U (H * b / ε)) (γ.V (H * b / ε)) / b +
      ‖S.theta (γ.U (H * b / ε)) (γ.V (H * b / ε)) /
        (S.lam (γ.U (H * b / ε)) (γ.V (H * b / ε)) : ℂ)‖ ^ 2 ≤ E := by
    rw [hrad] at hinit
    exact hinit.trans (mul_le_mul_of_nonneg_left hcooled (by norm_num))
  have hnext := hconnect c Λ F hc hF hF1 ui e (γ.U (H * b / ε)) x
    (γ.V (H * b / ε)) b E Bterm Jstop R₀ S g h hax hp.1 hxv hp.2.2.2
    hJ hb hbR hE hrad hbudget hrange hstop hcore hterm hg hg0 hmajor hJg hscale x
    ⟨hax, le_rfl⟩
  calc
    _ ≤ K * E := hnext.2.2
    _ = (2 * K * d) * ε + (2 * K * Cd) * σ ^ 2 := by dsimp only [E]; ring
    _ ≤ χ * ε + C₁ * σ ^ 2 := add_le_add
      (mul_le_mul_of_nonneg_right hcontract.le he.le)
      (mul_le_mul_of_nonneg_right (by dsimp only [C₁]; linarith) (sq_nonneg _))

end EmcsfAcExtension.Global
