module

public import EmcsfAcExtension.Local.Limit.AcBridgeSequence
public import EmcsfAcExtension.Local.Limit.AcBridgeMaxwellDensity
import EmcsfAcExtension.Local.Limit.AcBridgeUniform

/-! # The full general-AC Maxwell characteristic sequence record

internal project record item 7.6. The original sequence consists of broad
AC integral solutions. Constructed provenance and all strong current limits
are proved after broad identification, rather than assumed.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Full Maxwell characteristic convergence on the closed triangle. The two
current limits are the literal frozen Maxwell densities. All L¹ limits are
uniform over the entire indicated family of sections. -/
structure MaxwellCharacteristicLimit (e T : ℝ) (Sn : ℕ → Fields) (S : Fields) : Prop where
  /-- Each original charge section is outgoing AC. -/
  ac_out : ∀ n u, u ∈ Icc 0 T → AbsolutelyContinuousOnInterval ((Sn n).Q u) u T
  /-- Each original charge section is incoming AC. -/
  ac_in : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => (Sn n).Q u v) 0 v
  /-- The limiting charge is outgoing AC. -/
  limit_ac_out : ∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.Q u) u T
  /-- The limiting charge is incoming AC. -/
  limit_ac_in : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.Q u v) 0 v
  /-- Uniform charge convergence includes the axis. -/
  uniform_charge : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Q) (Function.uncurry S.Q)
      atTop (triangle 0 T)
  /-- Uniform convergence of the outgoing Maxwell polynomial. -/
  uniform_out_current : TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QV e))
      (Function.uncurry (S.QV e)) atTop (triangle 0 T)
  /-- Uniform convergence of the incoming Maxwell polynomial. -/
  uniform_in_current : TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QU e))
      (Function.uncurry (S.QU e)) atTop (triangle 0 T)
  /-- The outgoing limit density is the ordinary derivative sectionwise a.e. -/
  density_out : ∀ u ∈ Icc 0 T, deriv (S.Q u) =ᵐ[volume.restrict (Icc u T)] S.QV e u
  /-- The incoming limit density is the ordinary derivative sectionwise a.e. -/
  density_in : ∀ v ∈ Icc 0 T, deriv (fun u => S.Q u v) =ᵐ[volume.restrict (Icc 0 v)] (fun u => S.QU
      e u v)
  /-- Outgoing strong derivative convergence is uniform in the label. -/
  strong_out : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
    (∫ v in u..T, ‖deriv ((Sn n).Q u) v - deriv (S.Q u) v‖) < ρ
  /-- Incoming strong derivative convergence is uniform in the label. -/
  strong_in : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
    (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).Q u v) u - deriv (fun u => S.Q u v) u‖) < ρ
  /-- Every original regular-axis charge is zero. -/
  axis_charge : ∀ n t, t ∈ Icc 0 T → (Sn n).Q t t = 0
  /-- The limiting regular-axis charge is zero. -/
  limit_axis_charge : ∀ t ∈ Icc 0 T, S.Q t t = 0

/-- [internal]
The full general-AC Maxwell record, from the two authorized producer inputs.
The positive threshold depends only on the fixed box gap `c` and envelope
coefficient `H`, before time, coupling, common size, all data and solutions.
Current-to-L¹ passage retains the explicit length factor at most `T`.
No smoothness or constructed provenance is assumed of the original sequence. -/
theorem maxwell_characteristic_ac_limit_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt)
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s : ℝ, 0 < s ∧
      ∀ (T e η M Cb : ℝ) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ)
        (Sn : ℕ → Fields) (Jn Kn : ℕ → ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        (∀ n, AbsolutelyContinuousOnInterval (hn n) 0 T) →
        (∀ n, IsSolution e (Sn n) (triangle 0 T)) →
        (∀ n, IsRestartData (Sn n) (hn n) T) →
        (∀ n, StabBox (Sn n) c Cb η M (triangle 0 T)) →
        (∀ n, IntervalIntegrable (Jn n) volume 0 T) →
        (∀ n, IntervalIntegrable (Kn n) volume 0 T) →
        (∀ n u, u ∈ Icc 0 T → ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut (Sn n) u v‖ ≤ Jn n v) →
        (∀ n v, v ∈ Icc 0 T → ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e (Sn n) u v‖ ≤ Kn n u) →
        (∀ n, (∫ v in (0 : ℝ)..T, Jn n v) + (∫ u in (0 : ℝ)..T, Kn n u) ≤ H * η) →
        η ^ 2 + sigma e M T ≤ s →
        Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0) →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          MaxwellCharacteristicLimit e T Sn S := by
  obtain ⟨s,B,C,hs,_,hC,hcore⟩ := ac_sequence_comparisons_of_inputs hex hstab c H hc hH
  refine ⟨s,hs,?_⟩
  intro T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn hbox hJn _hKn hjn hkn hmass hsmall hd
  have hJmass n : (∫ v in (0 : ℝ)..T, Jn n v) ≤ H * η := by
    have hK0 : 0 ≤ ∫ u in (0 : ℝ)..T, Kn n u := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hT.le
      filter_upwards [hkn n T ⟨hT.le,le_rfl⟩] with u hu
      exact (norm_nonneg _).trans hu
    linarith only [hmass n, hK0]
  obtain ⟨S,hS,hdS,_,_,hM,hcons,hpair⟩ := hcore T e η M Cb hn h Sn Jn hT hη hac hacn hSn hdn hbox
      hJn
    (fun n => hjn n 0 ⟨le_rfl,hT.le⟩) hJmass hsmall hd
  obtain ⟨_,_,hr,_,_,hp,_,hθ,hξ⟩ := ac_uniform_limits_of_comparisons hT hc hC hSn hS hbox
    (fun n => (hcons n).2.2) hM (fun n => ⟨(hpair n).1,(hpair n).2.1⟩) hd
  obtain ⟨hqv,hqu,hstrongv,hstrongu⟩ := charge_strong_limits_of_primary_uniform hT hSn hS hr hp hθ
      hξ
  have ho (F : Fields) (hF : IsSolution e F (triangle 0 T)) u (hu : u ∈ Icc 0 T) :
      AbsolutelyContinuousOnInterval (F.Q u) u T :=
    (hF.ac_out u u T hu.2 (by rintro ⟨x,y⟩ ⟨rfl,hy⟩; exact ⟨hu.1,hy.1,hy.2⟩)).2.2.1
  have hi (F : Fields) (hF : IsSolution e F (triangle 0 T)) v (hv : v ∈ Icc 0 T) :
      AbsolutelyContinuousOnInterval (fun u => F.Q u v) 0 v :=
    (hF.ac_in 0 v v hv.1 (by rintro ⟨x,y⟩ ⟨hx,hxv,rfl⟩; exact ⟨hx,hxv,hv.2⟩)).2.2.1
  exact ⟨S,hS,hdS,⟨fun n => ho _ (hSn n), fun n => hi _ (hSn n), ho _ hS, hi _ hS,
    charge_uniform_of_current_uniform hT hSn hS hqv, hqv,hqu,hS.charge_derivatives_ae.1,
    hS.charge_derivatives_ae.2,hstrongv,hstrongu,
    fun n t ht => ((hSn n).axis t ⟨ht.1,le_rfl,ht.2⟩).2.2.1,
    fun t ht => (hS.axis t ⟨ht.1,le_rfl,ht.2⟩).2.2.1⟩⟩

end EmcsfAcExtension.Local
