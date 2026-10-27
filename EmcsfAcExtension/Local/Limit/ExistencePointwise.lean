module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Limit.StabilityPointwise

/-! # Pointwise bounds for the constructed primary limit

All estimates retain the smooth a priori constant and the original datum
variation. Axis mass ratios are handled using their frozen zero values.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- The actual frozen mass ratios converge on every point of a classical
strong limit with positive off-axis radius. The zero-axis case uses the
radius trace, without a lower bound on the radius at the axis. -/
theorem StrongLimit.tendsto_mu_of_radius_pos {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hlim : StrongLimit e T Sn S)
    (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    Tendsto (fun n => (Sn n).mu p.1 p.2) atTop (𝓝 (S.mu p.1 p.2)) := by
  rcases hp.2.1.eq_or_lt with heq | hlt
  · have ht : p.1 ∈ Icc 0 T := ⟨hp.1, hp.2.1.trans hp.2.2⟩
    have hz := hlim.axis_radius_of_c1 hc1 p.1 ht
    have hzn n := ((hc1 n).axis p.1 ⟨ht.1, le_rfl, ht.2⟩).1
    simpa only [← heq, Fields.mu, hz, hzn, div_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · exact ((hlim.unif_m.tendsto_at hp).const_mul 2).div (hlim.unif_r.tendsto_at hp)
      (hr p hp hlt).ne'

/-- Pass the five pointwise smooth a priori estimates to the frozen primary
limit. `C` retains its original scope: fixed before coupling, time, datum and
approximants. The scalar background is exactly `datumM h T` and the variation
is exactly `datumVar h T`; no enlarged datum size replaces either quantity. -/
theorem StrongLimit.pointwise_bounds_of_smoothBounds
    {C e T : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ} {S : Fields} {h : ℝ → ℂ}
    (hlim : StrongLimit e T Sn S)
    (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, S.lam p.1 p.2 ≠ 0)
    (hnu : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 ≠ 0)
    (hvertex : ∀ n, hn n 0 = h 0)
    (hvar : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)))
    (hb : ∀ n, SmoothBounds C e T (datumVar (hn n) T) (datumM (hn n) T) (Sn n)) :
    ∀ p ∈ triangle 0 T,
      0 ≤ S.mu p.1 p.2 ∧
      ‖S.phi p.1 p.2‖ ≤ datumM h T ∧
      ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ C * datumVar h T ∧
      |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤ C * datumVar h T ^ 2 ∧
      |S.Q p.1 p.2| ≤ C * |e| * datumM h T * datumVar h T * S.r p.1 p.2 ^ 2 := by
  have hM : Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) := by
    unfold datumM
    simpa only [hvertex] using tendsto_const_nhds.add (hvar.const_mul 10)
  intro p hp
  have hm := hlim.tendsto_mu_of_radius_pos hc1 hr hp
  have hLam := hlim.unif_lam.tendsto_at hp
  have hNu := hlim.unif_nu.tendsto_at hp
  have hθ := (hlim.unif_theta.tendsto_at hp).div
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hLam) (Complex.ofReal_ne_zero.mpr (hl p
        hp))
  have hξ := (hlim.unif_xi.tendsto_at hp).div
    (Complex.continuous_ofReal.continuousAt.tendsto.comp hNu) (Complex.ofReal_ne_zero.mpr (hnu p
        hp))
  refine ⟨ge_of_tendsto hm (Eventually.of_forall fun n => (hb n).mu_nonneg p hp),
    le_of_tendsto_of_tendsto (hlim.unif_phi.tendsto_at hp).norm hM
      (Eventually.of_forall fun n => (hb n).phi_le p hp),
    le_of_tendsto_of_tendsto (hθ.norm.add hξ.norm) (hvar.const_mul C)
      (Eventually.of_forall fun n => (hb n).ratio p hp),
    le_of_tendsto_of_tendsto (((hLam.sub_const (1 / 2)).abs.add (hNu.add_const (1 / 2)).abs).add hm)
      ((hvar.pow 2).const_mul C) (Eventually.of_forall fun n => (hb n).geom p hp),
    le_of_tendsto_of_tendsto (hlim.unif_Q.tendsto_at hp).abs
      (((hM.const_mul (C * |e|)).mul hvar).mul ((hlim.unif_r.tendsto_at hp).pow 2))
      (Eventually.of_forall fun n => (hb n).charge p hp)⟩

end EmcsfAcExtension.Local
