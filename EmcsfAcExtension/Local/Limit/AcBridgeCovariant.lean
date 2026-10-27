module

public import EmcsfAcExtension.Local.Limit.AcBridgeParallel
public import EmcsfAcExtension.Local.Limit.AcBridgeMixed
public import EmcsfAcExtension.Local.Limit.AcBridgeIntegrals
import EmcsfAcExtension.Infra.Triangle

/-! # Own-connection and transported incoming strong scalar limits

internal project record item 7.5. Continuous connection terms converge uniformly. The
unitary parallel factors then preserve the strong covariant derivative limit.
No incoming derivative of the connection is used in this scalar argument.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem cont_b {e T : ℝ} {S : Fields} (hS : IsSolution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry S.b) (triangle 0 T) :=
  hS.cont_phi.add (hS.cont_xi.div (Complex.continuous_ofReal.comp_continuousOn hS.cont_nu)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne))

private theorem cont_connection {e T : ℝ} {S : Fields} (hS : IsSolution e S (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => I * e * S.A p.1 p.2 * S.b p.1 p.2) (triangle 0 T) :=
  ((continuousOn_const (c := I * (e : ℂ))).mul
    (Complex.continuous_ofReal.comp_continuousOn hS.cont_A)).mul (cont_b hS)

/-- Ordinary strong incoming derivative convergence upgrades to convergence
of own-connection derivatives and actual transported derivatives. The supplied
`L` bounds the limiting covariant variation uniformly over sections and is
retained explicitly in the phase-multiplier estimate. No smoothness or extra
potential-derivative estimate is a premise of this scalar helper. -/
theorem covariant_scalar_limits_of_ordinary {e T L : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hL : 0 ≤ L)
    (hSn : ∀ n, IsSolution e (Sn n) (triangle 0 T)) (hS : IsSolution e S (triangle 0 T))
    (hbn : ∀ n v, v ∈ Icc 0 T → AbsolutelyContinuousOnInterval (fun u => (Sn n).b u v) 0 v)
    (hb : ∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v)
    (hvar : ∀ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v ≤ ENNReal.ofReal L)
    (hAl : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).A) (Function.uncurry S.A) atTop
        (triangle 0 T))
    (hbl : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).b) (Function.uncurry S.b) atTop
        (triangle 0 T))
    (hDl : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) < ρ) :
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e (Sn n) u v - incomingCovDeriv e S u v‖) < ρ) ∧
    TendstoUniformlyOn
      (fun n p => incomingParallel e (Sn n).A p.1 p.2 * (Sn n).b p.1 p.2)
      (fun p => incomingParallel e S.A p.1 p.2 * S.b p.1 p.2) atTop (triangle 0 T) ∧
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v,
        ‖deriv (fun u => incomingParallel e (Sn n).A u v * (Sn n).b u v) u -
          deriv (fun u => incomingParallel e S.A u v * S.b u v) u‖) < ρ) := by
  have hAc := Complex.isometry_ofReal.uniformContinuous.comp_tendstoUniformlyOn hAl
  have hcoef := (uniformContinuous_mul_left' (I * (e : ℂ))).comp_tendstoUniformlyOn hAc
  have hconnection := Mixed.tendstoUniformlyOn_mul_of_isCompact (isCompact_triangle 0 T)
    (fun n => (continuousOn_const (c := I * (e : ℂ))).mul
      (Complex.continuous_ofReal.comp_continuousOn (hSn n).cont_A))
    (fun n => cont_b (hSn n)) hcoef hbl
  have hconnection' := (section_integrals_tendsto_of_uniform hT
    (Fn := fun n u v => I * e * (Sn n).A u v * (Sn n).b u v)
    (f := fun u v => I * e * S.A u v * S.b u v)
    (fun n => cont_connection (hSn n)) (cont_connection hS) hconnection).2
  have hiA (v : ℝ) (hv : v ∈ Icc 0 T) : ContinuousOn (fun u => S.A u v) (Icc 0 v) :=
    hS.cont_A.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)
  have hiAn n (v : ℝ) (hv : v ∈ Icc 0 T) : ContinuousOn (fun u => (Sn n).A u v) (Icc 0 v) :=
    (hSn n).cont_A.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)
  have hiConn n v (hv : v ∈ Icc 0 T) :
      IntervalIntegrable (fun u => I * e * (Sn n).A u v * (Sn n).b u v) volume 0 v :=
    ((cont_connection (hSn n)).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)).intervalIntegrable_of_Icc hv.1
  have hiConnS v (hv : v ∈ Icc 0 T) :
      IntervalIntegrable (fun u => I * e * S.A u v * S.b u v) volume 0 v :=
    ((cont_connection hS).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)).intervalIntegrable_of_Icc hv.1
  have hown := incoming_sum_strong_of_strong
    (Fn := fun n u v => deriv (fun u => (Sn n).b u v) u)
    (Gn := fun n u v => I * e * (Sn n).A u v * (Sn n).b u v)
    (f := fun u v => deriv (fun u => S.b u v) u)
    (g := fun u v => I * e * S.A u v * S.b u v)
    (fun n v hv => (hbn n v hv).intervalIntegrable_deriv_complex) hiConn
    (fun v hv => (hb v hv).intervalIntegrable_deriv_complex) hiConnS hDl hconnection'
  have hown' : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e (Sn n) u v - incomingCovDeriv e S u v‖) < ρ := hown
  have hP := incoming_parallel_uniform_of_potential_uniform (e := e) hT
    (fun n => (hSn n).cont_A) hS.cont_A hAl
  have hPnac n v (hv : v ∈ Icc 0 T) := incomingParallel_ac_of_continuous (e := e) hv.1 (hiAn n v hv)
  have hPac v (hv : v ∈ Icc 0 T) := incomingParallel_ac_of_continuous (e := e) hv.1 (hiA v hv)
  have hinc n v (hv : v ∈ Icc 0 T) := incoming_covDeriv_integral_of_ac (e := e) hv.1 (hiAn n v hv)
      (hbn n v hv)
  have hincS v (hv : v ∈ Icc 0 T) := incoming_covDeriv_integral_of_ac (e := e) hv.1 (hiA v hv) (hb v
      hv)
  have hbound v (hv : v ∈ Icc 0 T) : (∫ u in (0 : ℝ)..v, ‖incomingCovDeriv e S u v‖) ≤ L := by
    rw [(hincS v hv).2]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar v hv)).trans_eq (ENNReal.toReal_ofReal
        hL)
  have hprod := incoming_unitary_strong_of_strong hL
    (fun n v hv => by simpa only [uIcc_of_le hv.1] using (hPnac n v hv).continuousOn)
    (fun v hv => by simpa only [uIcc_of_le hv.1] using (hPac v hv).continuousOn)
    (fun n v hv => (hinc n v hv).1) (fun v hv => (hincS v hv).1)
    (fun n p _ => norm_incomingParallel e (Sn n).A p.1 p.2) hbound hP hown'
  obtain ⟨B,hB⟩ := (isCompact_triangle 0 T).bddAbove_image (cont_b hS).norm
  have hBu : ∀ p ∈ triangle 0 T, ‖S.b p.1 p.2‖ ≤ max 0 B :=
    fun p hp => (hB (mem_image_of_mem _ hp)).trans (le_max_right _ _)
  refine ⟨hown', unitary_product_uniform_of_uniform (le_max_left _ _) hP hbl
    (fun n p _ => norm_incomingParallel e (Sn n).A p.1 p.2) hBu, ?_⟩
  intro ρ hρ
  obtain ⟨N,hN⟩ := hprod ρ hρ
  refine ⟨N, fun n hn v hv => ?_⟩
  have heq : (∫ u in (0 : ℝ)..v,
      ‖deriv (fun u => incomingParallel e (Sn n).A u v * (Sn n).b u v) u -
        deriv (fun u => incomingParallel e S.A u v * S.b u v) u‖) =
      ∫ u in (0 : ℝ)..v, ‖incomingParallel e (Sn n).A u v * incomingCovDeriv e (Sn n) u v -
        incomingParallel e S.A u v * incomingCovDeriv e S u v‖ := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hv.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (incoming_parallel_ac_deriv_of_ac (e := e) hv.1 (hiAn n v hv) (hbn n v hv)).2,
      ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
        (incoming_parallel_ac_deriv_of_ac (e := e) hv.1 (hiA v hv) (hb v hv)).2] with u hun hus
    rw [hun, hus]
  rw [heq]
  exact hN n hn v hv

end EmcsfAcExtension.Local
