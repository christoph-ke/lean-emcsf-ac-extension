module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.WaveSystemPicard
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Classical axis construction and the geometry of the corner

The local solutions below consume precisely the pending Picard and full-system
inputs. They do not assume a future-axis trace. All node readings in this file
are the C¹ readings authorized for the construction route by internal project record.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A full-width construction wedge is exactly the closed triangle,
including its terminal apex. -/
theorem continuationWedge_full (c L : ℝ) :
    continuationWedge c L L = triangle c (c + L) := by
  ext p
  constructor
  · exact fun hp => hp.1
  · intro hp
    exact ⟨hp, hp.2.1.trans hp.2.2⟩

/-- The original local wedge contains its positive initial full triangle. -/
theorem triangle_subset_continuationWedge {a T : ℝ} (haT : a ≤ T) :
    triangle 0 a ⊆ continuationWedge 0 a T := by
  intro p hp
  exact ⟨⟨hp.1, hp.2.1, by simpa using hp.2.2.trans haT⟩,
    by simpa using hp.2.1.trans hp.2.2⟩

/-- Initial values of a literal carrier fixed point. The normalized scalar
identity uses the positive expansion, and holds at the existing vertex. -/
theorem ContinuationPair.cone_values_of_fixedPoint {c a L e : ℝ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} {Z : ContinuationPair c a L}
    (ha : 0 ≤ a) (hfix : Z.IsFixedPoint e lam₀ h₀)
    (hpos : ∀ p ∈ continuationWedge c a L, 0 < Z.lam p.1 p.2) :
    ∀ v ∈ Icc c (c + L),
      (Recon.toFields e Z.lam Z.hh).lam c v = lam₀ v ∧
      (Recon.toFields e Z.lam Z.hh).a c v = h₀ v := by
  intro v hv
  have hp : (c, v) ∈ continuationWedge c a L :=
    ⟨⟨le_rfl, hv⟩, by dsimp; linarith⟩
  obtain ⟨hL, hH⟩ := hfix (c, v) hp
  obtain ⟨hl, hh⟩ := Recon.cone_values_of_picard hL hH
  refine ⟨hl, ?_⟩
  have hne : (Z.lam c v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos _ hp).ne'
  change Recon.phi Z.lam Z.hh c v +
    (Z.lam c v : ℂ) * (Z.hh c v - Recon.phi Z.lam Z.hh c v) /
      (Z.lam c v : ℂ) = h₀ v
  rw [mul_div_cancel_left₀ _ hne]
  linear_combination hh

/-- The reconstructed connection has zero gauge on every axis point.
This is an integral identity and imposes no future trace as input. -/
theorem continuation_reconstruction_axis_gauge (e : ℝ)
    (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ) (t : ℝ) :
    (Recon.toFields e lam hh).A t t = 0 := by
  simp [Recon.toFields, Recon.A]

/-- Normalized initial radius from the literal radial primitive and the
initial expansion `1/2` on the entire entering cone. -/
theorem continuation_reconstruction_initial_radius {T e : ℝ}
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    (hl : ∀ v ∈ Icc 0 T, lam 0 v = 1 / 2) :
    ∀ v ∈ Icc 0 T, (Recon.toFields e lam hh).r 0 v = v / 2 := by
  intro v hv
  change (∫ s in (0 : ℝ)..v, lam 0 s) = v / 2
  calc
    _ = ∫ _s in (0 : ℝ)..v, (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hv.1] at hs
      exact hl s ⟨hs.1, hs.2.trans hv.2⟩
    _ = v / 2 := by simp [div_eq_mul_inv]

/-- [internal]
In the C¹ reading of charged_SF_new_version.tex:L6064–6086, the exact paper map on
the complete canonical ball has its incoming-width Lipschitz coefficient
`a*C<1`, preserves that ball, and has a Banach fixed point in the full
closed outgoing-jet carrier. The pending internal project record input supplies the
literal ball and estimates; Banach's theorem is applied here through the
proved adapter. The width depends only on the fixed first-datum class. -/
theorem smooth_local_fixedPoint_of_inputs
    (hPicard : ContinuationOriginalPicardInput)
    {T e : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hh : ContDiffOn ℝ 1 h (Icc 0 T))
    (hε : datumVar h T ≤ 1 / 64) (hδ : |e| * datumM h T * T ≤ 1 / 16) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧
      ∃ _ball : ContinuationPicardBall e 0 a T (fun _ => 1/2) h
          (1/128) (1/2-1/128) (3/4),
      ∃ Z : ContinuationPair 0 a T,
        Z.IsFixedPoint e (fun _ => 1/2) h ∧ Z.InConeBall (fun _ => 1/2) h (1/128) ∧
        ∀ p ∈ continuationWedge 0 a T,
          1/2-1/128 ≤ Z.lam p.1 p.2 ∧ 3/4 ≤ 1-Recon.mu e Z.lam Z.hh p.1 p.2 := by
  have hd := hh.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.bddAbove_image hd.norm
  let D := max 0 D₀
  have hM : 1 ≤ datumM h T := by
    dsimp only [datumM]
    have hv : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
    have hn := norm_nonneg (h 0)
    linarith
  obtain ⟨C,a,_hC,ha,haT,_hCa,hlocal⟩ :=
    hPicard T |e| (datumM h T) D hT (abs_nonneg e) hM (le_max_left _ _)
  obtain ⟨ball,_hcoeff⟩ := hlocal e h rfl rfl hh
    (fun v hv => (hD₀ (mem_image_of_mem _ hv)).trans (le_max_right _ _)) hε hδ
  obtain ⟨Z,hfix,hball,hbounds⟩ := ball.exists_fixedPoint ha
  exact ⟨a,ha,haT,ball,Z,hfix,hball,hbounds⟩

/-- Original-cone full-system existence from the complete Picard-ball
and C¹ recovery inputs. The local width may depend on the datum's first
derivative; the smallness thresholds and canonical background are fixed. -/
theorem smooth_local_solution_of_inputs
    (hPicard : ContinuationOriginalPicardInput) (hRecovery : ContinuationRecoveryInput)
    {T e : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hh : ContDiffOn ℝ 1 h (Icc 0 T))
    (hε : datumVar h T ≤ 1 / 64) (hδ : |e| * datumM h T * T ≤ 1 / 16) :
    ∃ (a : ℝ) (F : Fields), 0 < a ∧ a ≤ T ∧
      IsC1Solution e F (continuationWedge 0 a T) ∧ IsRestartData F h T := by
  obtain ⟨a,ha,haT,_ball,Z,hfix,_hball,hbounds⟩ :=
    smooth_local_fixedPoint_of_inputs hPicard hT hh hε hδ
  have hc : ContDiffOn ℝ 1 h (Icc 0 (0 + T)) := by simpa using hh
  have hS := hRecovery 0 a T e (1 / 2 - 1 / 128) (3 / 4)
    (fun _ => 1 / 2) h Z ha haT (by norm_num) (by norm_num) contDiffOn_const
    hc hbounds hfix
  have hpos p (hp : p ∈ continuationWedge 0 a T) : 0 < Z.lam p.1 p.2 :=
    lt_of_lt_of_le (by norm_num) (hbounds p hp).1
  have hcone := Z.cone_values_of_fixedPoint ha.le hfix hpos
  have hl : ∀ v ∈ Icc 0 T, Z.lam 0 v = 1 / 2 := by
    intro v hv
    exact (hcone v (by simpa using hv)).1
  refine ⟨a, Recon.toFields e Z.lam Z.hh, ha, haT, hS, ?_, ?_⟩
  · intro v hv
    exact ⟨continuation_reconstruction_initial_radius hl v hv,
      (hcone v (by simpa using hv)).2⟩
  · intro t _ht
    exact continuation_reconstruction_axis_gauge e Z.lam Z.hh t

/-- Uniform C¹ solution on a short later cone. The time is chosen before
cone position and data, from exactly the four cone value/jet bounds,
the lower expansion and the coupling. There is no future-axis premise. -/
theorem short_cone_solution_of_inputs
    (hPicard : ContinuationShortPicardInput) (hRecovery : ContinuationRecoveryInput)
    (B ℓ e : ℝ) (hB : 1 ≤ B) (hℓ : 0 < ℓ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
        ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
        ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
        (∀ v ∈ Icc c (c + L), ℓ ≤ lam₀ v ∧ |lam₀ v| ≤ B ∧ ‖h₀ v‖ ≤ B ∧
          |derivWithin lam₀ (Icc c (c + L)) v| ≤ B ∧
          ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ B) →
        ∃ F : Fields, IsC1Solution e F (triangle c (c + L)) ∧
          (∀ v ∈ Icc c (c + L), F.lam c v = lam₀ v ∧ F.a c v = h₀ v) ∧
          ∀ t ∈ Icc c (c + L), F.A t t = 0 := by
  obtain ⟨τ, hτ, hlocal⟩ := hPicard B ℓ |e| hB hℓ (abs_nonneg e)
  refine ⟨τ, hτ, ?_⟩
  intro c L lam₀ h₀ hL hLτ cl ch hdata
  obtain ⟨Z, hfix, _hball, hbounds⟩ := hlocal e rfl c L lam₀ h₀ hL hLτ cl ch hdata
  have hS := hRecovery c L L e (ℓ / 2) (3 / 4) lam₀ h₀ Z hL le_rfl
    (by positivity) (by norm_num) cl ch hbounds hfix
  refine ⟨Recon.toFields e Z.lam Z.hh, ?_, ?_, ?_⟩
  · simpa only [continuationWedge_full] using hS
  · exact Z.cone_values_of_fixedPoint hL.le hfix
      (fun p hp => lt_of_lt_of_le (by positivity) (hbounds p hp).1)
  · intro t _ht
    exact continuation_reconstruction_axis_gauge e Z.lam Z.hh t

/-- The precise old/strip overlap with a later corner is a complete
axis triangle together with a positive-radius rectangle. This equality
includes the two common sides and the terminal boundary. -/
theorem continuation_axis_overlap_geometry {c d S b : ℝ}
    (hc : 0 ≤ c) (hdS : d ≤ S) (hSb : S ≤ b) :
    (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) ∩ triangle c b =
      triangle c S ∪ (Icc c d ×ˢ Icc S b) := by
  ext p
  constructor
  · rintro ⟨hp | hp, hpC⟩
    · exact Or.inl ⟨hpC.1, hp.2⟩
    · exact Or.inr ⟨⟨hpC.1, hp.1.2⟩, hp.2⟩
  · rintro (hp | hp)
    · exact ⟨Or.inl ⟨hc.trans hp.1, hp.2⟩,
        ⟨hp.1, hp.2.1, hp.2.2.trans hSb⟩⟩
    · exact ⟨Or.inr ⟨⟨hc.trans hp.1.1, hp.1.2⟩, hp.2⟩,
        ⟨hp.1.1, hp.1.2.trans (hdS.trans hp.2.1), hp.2.2⟩⟩

/-- The wider strip gives a full-dimensional common domain with the
axis corner, even at its closed seams. Consequently equality of the
nine fields on this overlap also determines equality of first jets. -/
theorem continuation_axis_overlap_uniqueDiff {c d S b : ℝ}
    (hc : 0 ≤ c) (hcd : c < d) (hdS : d < S) (hSb : S < b) :
    UniqueDiffOn ℝ
      ((triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) ∩ triangle c b) := by
  rw [continuation_axis_overlap_geometry hc hdS.le hSb.le]
  intro p hp
  rcases hp with hp | hp
  · exact (uniqueDiffOn_triangle (hcd.trans hdS) p hp).mono subset_union_left
  · exact (uniqueDiffOn_rectangle hcd hSb p hp).mono subset_union_right

/-- Choice of the corner parameters in the blueprint's required order.
The short-cone time is already fixed when `η` is selected. For every
strip height below `δ`, the capped cone has strictly smaller length
than `τ/4`; this includes the cap `b=T`. -/
theorem continuation_corner_parameters {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < s / 8 ∧ η < τ / 8 ∧
      ∀ δ : ℝ, 0 < δ → δ < min η (τ / 8) →
        ∀ T S : ℝ, S ≤ T → min T (S + δ) - (S - η) < τ / 4 := by
  let η := min s τ / 16
  have hη : 0 < η := div_pos (lt_min hs hτ) (by norm_num)
  have hηs : η < s / 8 := by
    have h := min_le_left s τ
    dsimp [η]
    linarith
  have hητ : η < τ / 8 := by
    have h := min_le_right s τ
    dsimp [η]
    linarith
  refine ⟨η, hη, hηs, hητ, ?_⟩
  intro δ _hδ hδ T S _hST
  have hδτ := hδ.trans_le (min_le_right _ _)
  have hcap := min_le_right T (S + δ)
  linarith

/-- [internal]
Common C¹ bounds and the uniform axis time in the C¹ reading of
charged_SF_new_version.tex:L6291–6293. The enlarged cone class and its time are
chosen before the maximal-apex candidate and `η`, as required by
internal project record:1075–1079 and the binding internal project record review.
Universal thresholds precede the datum; `B,Bc,ℓ,τ` may depend on
the fixed datum's C¹ norm, but precede all constructed apex coordinates.
The strip height remains a subsequent construction obligation. -/
theorem continuation_parameters_of_inputs
    (hBound : ContinuationC1BoundInput) (hPicard : ContinuationShortPicardInput)
    (hRecovery : ContinuationRecoveryInput) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T → ContDiffOn ℝ 1 h (Icc 0 T) →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ B Bc ℓ τ : ℝ, 0 < B ∧ 1 ≤ Bc ∧ 0 < ℓ ∧ 0 < τ ∧
          ℓ = B⁻¹ ∧
          Bc = 1 + 16 * (B + 1) * (1 + ℓ⁻¹) + 64 * (B + 1) ^ 2 * ℓ⁻¹ ^ 2 ∧
          (∀ (s : ℝ) (F : Fields), 0 < s → s ≤ T →
            IsC1Solution e F (triangle 0 s) → IsRestartData F h s →
            C1BoundOn F (triangle 0 s) B) ∧
          (∀ (c L : ℝ) (lam₀ : ℝ → ℝ) (h₀ : ℝ → ℂ), 0 < L → L ≤ τ →
            ContDiffOn ℝ 1 lam₀ (Icc c (c + L)) →
            ContDiffOn ℝ 1 h₀ (Icc c (c + L)) →
            (∀ v ∈ Icc c (c + L), ℓ / 2 ≤ lam₀ v ∧ |lam₀ v| ≤ Bc ∧
              ‖h₀ v‖ ≤ Bc ∧ |derivWithin lam₀ (Icc c (c + L)) v| ≤ Bc ∧
              ‖derivWithin h₀ (Icc c (c + L)) v‖ ≤ Bc) →
            ∃ F : Fields, IsC1Solution e F (triangle c (c + L)) ∧
              (∀ v ∈ Icc c (c + L), F.lam c v = lam₀ v ∧ F.a c v = h₀ v) ∧
              ∀ t ∈ Icc c (c + L), F.A t t = 0) ∧
          ∀ q : ℝ, 0 < q → q ≤ T →
            ∃ η : ℝ, 0 < η ∧ η < q / 8 ∧ η < τ / 8 := by
  obtain ⟨ε, δ, hε, hδ, hcommon⟩ := hBound
  refine ⟨ε, δ, hε, hδ, ?_⟩
  intro T e h hT hh hsmall hscale
  obtain ⟨B, hB, hbound⟩ := hcommon T e h hT hh hsmall hscale
  let ℓ := B⁻¹
  let Bc := 1 + 16 * (B + 1) * (1 + ℓ⁻¹) + 64 * (B + 1) ^ 2 * ℓ⁻¹ ^ 2
  have hℓ : 0 < ℓ := inv_pos.mpr hB
  have hBc : 1 ≤ Bc := by
    have hi : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
    have h1 : 0 ≤ 16 * (B + 1) * (1 + ℓ⁻¹) := by positivity
    have h2 : 0 ≤ 64 * (B + 1) ^ 2 * ℓ⁻¹ ^ 2 := by positivity
    dsimp only [Bc]
    linarith only [h1, h2]
  obtain ⟨τ, hτ, hlocal⟩ := short_cone_solution_of_inputs hPicard hRecovery
    Bc (ℓ / 2) e hBc (by positivity)
  refine ⟨B, Bc, ℓ, τ, hB, hBc, hℓ, hτ, rfl, rfl, hbound, hlocal, ?_⟩
  intro q hq _hqT
  obtain ⟨η, hη, hηq, hητ, _hfit⟩ := continuation_corner_parameters hq hτ
  exact ⟨η, hη, hηq, hητ⟩

end EmcsfAcExtension.Local
