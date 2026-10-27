module

public import EmcsfAcExtension.Local.Construction.PicardOriginalContraction
public import EmcsfAcExtension.Local.Construction.PicardOriginalBall
public import EmcsfAcExtension.Local.Construction.PicardBallFixedPoint
public import EmcsfAcExtension.Local.Construction.PicardShortConeContraction

/-! # The complete invariant-ball node

Universal original-data thresholds and the uniform short-cone construction
are both proved for the literal audited Picard map, on complete closed balls.
-/

public section

open Set
open scoped ENNReal ContDiff

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#picard-invariant-ball]
The C¹ original-data construction and uniform C¹ short-cone construction E5.
Original thresholds and radius are universal. Original time is chosen after
`(T,e,h)` and is uniform over bounds for `T,|e|,datumM h T` and its first
outgoing derivative, as `picardOriginalBall_uniform_contraction` makes explicit.
Short-cone radius and time depend only on `B,ell,|e|`, before cone and datum.
Both exact self-maps have contraction factor `1/2` and unique fixed points.
S1's expansion and gap are derived on every ball; S2 uses only `datumM`.
The initial fixed points are C0 in incoming time and C1 in outgoing time;
higher regularity is the separate smooth-regularity node. -/
theorem picard_invariant_ball :
    (∃ ε₀ > 0, ∃ δ₀ > 0, ∀ (T e : ℝ) (h : ℝ → ℂ) (hT : 0 < T)
      (hc : ContDiffOn ℝ 1 h (Icc 0 T)),
      datumVar h T ≤ ε₀ → chargedScale e h T ≤ δ₀ →
      ∃ (a : ℝ) (ha : 0 < a) (haT : a ≤ T), a ≤ 1 ∧
            let center := picardOriginalCenter ha.le haT h hT hc
            ∃ F : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128) →
                PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128),
              (∀ z p, (F z).1.1.1 p =
                picardUpdate ha.le haT e (fun _ => 1 / 2) h z.1 p.1.1 p.1.2) ∧
              (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
              (∃! z, F z = z) ∧
              (∀ (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)) p,
                (1 / 4 : ℝ) ≤ (z.1.1.1 p).1 ∧
                (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam ha.le haT z.1)
                  (picardCandidateH ha.le haT z.1) p.1.1 p.1.2)) ∧
    (∀ (B ell e : ℝ), 1 ≤ B → 0 < ell →
      ∃ ρ > 0, ρ ≤ 1 / 128 ∧ ρ ≤ ell / 4 ∧ ∃ τ > 0, τ ≤ 1 ∧
            ∀ (c L : ℝ) (hL : 0 < L), L ≤ τ →
            ∀ (datum : ℝ → ℝ × ℂ) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))),
            (∀ v ∈ Icc c (c + L),
              ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B) →
            (∀ v ∈ Icc c (c + L), ell ≤ (datum v).1) →
            let center := picardConeCenterOfContDiff (a := L) datum hL hc
            ∃ F : PicardBall datum center ρ → PicardBall datum center ρ,
              (∀ z p, (F z).1.1.1 p = picardUpdate hL.le le_rfl e
                (fun v => (datum v).1) (fun v => (datum v).2) z.1 p.1.1 p.1.2) ∧
              (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
              (∃! z, F z = z) ∧
              (∀ (z : PicardBall datum center ρ) p, ell / 2 ≤ (z.1.1.1 p).1 ∧
                (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam hL.le le_rfl z.1)
                  (picardCandidateH hL.le le_rfl z.1) p.1.1 p.1.2)) := by
  constructor
  · exact ⟨1 / 64, by norm_num, 1 / 32, by norm_num,
      fun _ _ _ hT hc hv hs => picardOriginalBall_contraction hT hc hv hs⟩
  · exact fun B ell e hB he => picardShortCone_contraction B ell e hB he

end EmcsfAcExtension.Local
