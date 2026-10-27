module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Frozen.IntegralForm
public import EmcsfAcExtension.Global.Observation.OuterScalar
import EmcsfAcExtension.Global.Observation.OuterMass
import EmcsfAcExtension.Global.Observation.InnerMass

/-! # Ordinary incoming derivative of the scalar comparison

The comparison is differentiated in the fixed boundary-parallel gauge.
The connection correction is retained, and the boundary value is kept at
its original incoming label. Source: charged_SF_new_version.tex:L2549–L2569 and
internal project record, incoming derivative transfer and scalar reconstruction.
-/

public section

open Complex Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [internal]
Differentiate the literal comparison variable using the characteristic
radius and scalar equations and the radial reference derivative. The
result is an ordinary derivative; its connection term has a minus sign.
No estimate or regularity of the incoming boundary datum is assumed. -/
theorem Observation.scalar_comparison_in_deriv_of_equations
    (S : Fields) (e : ℝ) (H : ℂ) (phiStar : ℝ → ℂ) {u v : ℝ} (yStar : ℂ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hdr : HasDerivAt (fun x => S.r x v) (S.nu u v) u)
    (hdphi : HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u)
    (hdf : HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r)
      (phiStar (S.r u v) + yStar) (S.r u v)) :
    HasDerivAt (fun x => scalarComparison S H phiStar x v)
      ((S.nu u v : ℂ) *
          (scalarComparison S H phiStar u v / S.r u v +
            S.xi u v / S.nu u v - yStar) -
        I * e * S.A u v * S.r u v * S.phi u v) u := by
  have hd := (hdr.ofReal_comp.mul (hdphi.sub_const H)).sub
    (hdf.scomp (h := fun x => S.r x v) u hdr)
  convert hd using 1
  · rfl
  · simp only [scalarComparison, shiftedRphi, Fields.phiU, real_smul]
    have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp [hrC, hnC]; ring

/-- [internal]
Integrating an ordinary mixed derivative transfers the incoming
derivative while retaining its boundary value at the same label. This
exact integral estimate has universal coefficient one. Its consumer
must supply the mixed equation and its source envelope from the outer
comparison; a bound on the boundary datum is not an input. -/
theorem Observation.incoming_derivative_transfer_of_integralForm
    {wU source : ℝ → ℂ} {g : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hform : IntegralForm wU source a b) (hb : wU b = -g / 2) :
    ‖wU a + g / 2‖ ≤ ∫ v in a..b, ‖source v‖ := by
  have heq : wU a + g / 2 = -(wU b - wU a) := by rw [hb]; ring
  rw [heq, norm_neg, hform.2]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-- [internal]
The ordinary incoming comparison derivative has the same outgoing mixed
derivative as the outgoing comparison derivative has incoming derivative.
This direct calculation uses only the outgoing characteristic equations;
it requires no second incoming derivative or interchange of rough traces.
The source includes the ordinary connection correction. -/
theorem Observation.incoming_mixed_deriv_of_normalization
    {S : Fields} {e u v kStar : ℝ} (H : ℂ) (phiStar yStar : ℝ → ℂ)
    (hr : S.r u v ≠ 0)
    (hR : HasDerivAt (S.r u) (S.lam u v) v)
    (hnu : HasDerivAt (S.nu u) (S.rUV u v) v)
    (hphi : HasDerivAt (S.phi u) (S.phiV u v) v)
    (hxi : HasDerivAt (S.xi u) (S.xiV e u v) v)
    (hA : HasDerivAt (S.A u) (S.AV u v) v)
    (hstatic : HasDerivAt (fun r => phiStar r + yStar r)
      ((-kStar / S.r u v : ℝ) * yStar (S.r u v)) (S.r u v)) :
    let k := (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
    let wV := (S.lam u v : ℂ) *
      (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v
    HasDerivAt (fun s => (S.nu u s : ℂ) *
      (S.phi u s - H - (phiStar (S.r u s) + yStar (S.r u s))) + S.xi u s -
        I * e * S.A u s * S.r u s * S.phi u s)
      (-(((-S.nu u v) * S.lam u v * k / S.r u v ^ 2 : ℝ) : ℂ) *
          scalarComparison S H phiStar u v +
        (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) *
          yStar (S.r u v) * (k - kStar) -
        I * e * S.A u v * S.lam u v *
          (H + (phiStar (S.r u v) + yStar (S.r u v))) +
        I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v : ℝ) * S.r u v ^ 2 : ℝ) *
          (shiftedRphi S H u v + S.r u v * H) - I * e * S.A u v * wV) v := by
  convert ((hnu.ofReal_comp.mul
    ((hphi.sub_const H).sub (hstatic.scomp v hR))).add hxi).sub
      (((hA.ofReal_comp.const_mul (I * e)).mul hR.ofReal_comp).mul hphi) using 1
  · funext s
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  · dsimp only [Fields.rUV, Fields.phiV, Fields.xiV, Fields.AV, Fields.waveSource,
      scalarComparison, shiftedRphi]
    simp only [real_smul, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
    ring

/-- [internal]
An outward ordinary derivative with the outer neutral/electric envelope
transfers the incoming comparison derivative at the same label. The
optical coefficient is the universal `8`. The finite outer endpoint and
electric logarithm are retained, uniformly in both endpoints and data.
The consumer supplies the literal mixed derivative computed above. -/
theorem Observation.incoming_transfer_of_source_envelope
    {wU source : ℝ → ℂ} {R lam : ℝ → ℝ} {g : ℂ}
    {a b rho L A E : ℝ} (hab : a ≤ b) (hrho : 0 < rho)
    (hR : ∀ s ∈ Icc a b, HasDerivAt R (lam s) s)
    (hlam : ContinuousOn lam (Icc a b))
    (hrad : ∀ s ∈ Icc a b, R s ∈ Icc rho L)
    (hspeed : ∀ s ∈ Icc a b, 1 / 8 ≤ lam s) (hRb : R b = L)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hform : IntegralForm wU source a b) (hb : wU b = -g / 2)
    (hsource : ∀ s ∈ Icc a b,
      ‖source s‖ ≤ A / R s ^ 3 + E / R s ^ 4 + E / (L * R s)) :
    ‖wU a + g / 2‖ ≤
      8 * A / R a ^ 2 + 8 * E / R a ^ 3 + 8 * E / L * Real.log (L / R a) := by
  let f : ℝ → ℝ := fun r => A / r ^ 3 + E / r ^ 4 + E / (L * r)
  have hL : 0 < L := hrho.trans_le (hrad a ⟨le_rfl, hab⟩).1 |>.trans_le
    (hrad a ⟨le_rfl, hab⟩).2
  have hf : ContinuousOn f (Icc rho L) :=
    ((continuousOn_const.div (continuousOn_id.pow 3)
      (fun s hs => pow_ne_zero 3 (hrho.trans_le hs.1).ne')).add
      (continuousOn_const.div (continuousOn_id.pow 4)
      (fun s hs => pow_ne_zero 4 (hrho.trans_le hs.1).ne'))).add
      (continuousOn_const.div (continuousOn_const.mul continuousOn_id)
      (fun s hs => mul_ne_zero hL.ne' (hrho.trans_le hs.1).ne'))
  have hRc : ContinuousOn R (Icc a b) :=
    fun s hs => (hR s hs).continuousAt.continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab hform.1.norm
    ((hf.comp hRc hrad).intervalIntegrable_of_Icc hab) hsource
  have hradial := radial_section_integral_le (σ := 1) hab hR hlam hrad hf
    (fun s hs => by dsimp [f]; have hp := hrho.trans_le hs.1; positivity)
    (fun s hs => by linarith only [hspeed s hs])
  rw [hRb] at hradial
  have hkernel := incoming_kernel_integral (hrho.trans_le (hrad a ⟨le_rfl, hab⟩).1)
    (hrad a ⟨le_rfl, hab⟩).2 hA hE
  exact (Observation.incoming_derivative_transfer_of_integralForm hab hform hb).trans
    (hm.trans (hradial.trans ((mul_le_mul_of_nonneg_left hkernel (by norm_num)).trans_eq
      (by ring))))

/-- [internal]
Transfer the literal incoming comparison derivative after the outer
source, potential and outgoing-derivative estimates. The neutral
coefficient is `8*Cn`; the electric coefficient is `8*(Ce+Cp*Bv)`.
All four coefficients are fixed before the fields, scales and errors.
The exact outgoing mixed equation is supplied by normalization, and
the boundary term keeps the same label and its unsquared value. -/
theorem Observation.incoming_derivative_transfer_of_outer
    {S : Fields} {e u v rho L Nphi Nm Cn Ce Cp Bv eta : ℝ}
    (H : ℂ) (phiStar yStar : ℝ → ℂ) (wV source : ℝ → ℂ)
    (hvu : v ≤ u) (hrho : 0 < rho) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce)
    (hCp : 0 ≤ Cp) (hBv : 0 ≤ Bv) (hNp : 0 ≤ Nphi) (hNm : 0 ≤ Nm) (heta : 0 ≤ eta)
    (hR : ∀ s ∈ Icc v u, HasDerivAt (S.r u) (S.lam u s) s)
    (hlam : ContinuousOn (S.lam u) (Icc v u))
    (hAc : ContinuousOn (S.A u) (Icc v u)) (hVc : ContinuousOn wV (Icc v u))
    (hsc : ContinuousOn source (Icc v u))
    (hrad : ∀ s ∈ Icc v u, S.r u s ∈ Icc rho L)
    (hspeed : ∀ s ∈ Icc v u, 1 / 8 ≤ S.lam u s)
    (hRL : S.r u u = L) (hnu : S.nu u u = -1 / 2) (hA : S.A u u = 0)
    (hstar : phiStar L + yStar L = 0)
    (hwc : ContinuousOn (fun s => (S.nu u s : ℂ) *
      (S.phi u s - H - (phiStar (S.r u s) + yStar (S.r u s))) + S.xi u s -
        I * e * S.A u s * S.r u s * S.phi u s) (Icc v u))
    (hd : ∀ s ∈ Ioo v u, HasDerivAt (fun s => (S.nu u s : ℂ) *
      (S.phi u s - H - (phiStar (S.r u s) + yStar (S.r u s))) + S.xi u s -
        I * e * S.A u s * S.r u s * S.phi u s)
        (source s - I * e * S.A u s * wV s) s)
    (hsource : ∀ s ∈ Icc v u,
      ‖source s‖ ≤ Cn * (Nphi + Nm) / (S.r u s) ^ 3 +
        Ce * (eta / (S.r u s) ^ 4 + eta / (L * S.r u s)))
    (hpotential : ∀ s ∈ Icc v u, |e * S.A u s| ≤ Cp * eta / (L * S.r u s))
    (hV : ∀ s ∈ Icc v u, ‖wV s‖ ≤ Bv) :
    ‖((S.nu u v : ℂ) * (S.phi u v - H -
      (phiStar (S.r u v) + yStar (S.r u v))) + S.xi u v -
        I * e * S.A u v * S.r u v * S.phi u v) +
      (S.phi u u - H + S.xi u u / S.nu u u) / 2‖ ≤
        8 * (Cn * (Nphi + Nm)) / (S.r u v) ^ 2 +
          8 * ((Ce + Cp * Bv) * eta) / (S.r u v) ^ 3 +
            8 * ((Ce + Cp * Bv) * eta) / L * Real.log (L / S.r u v) := by
  let wU := fun s => (S.nu u s : ℂ) *
    (S.phi u s - H - (phiStar (S.r u s) + yStar (S.r u s))) + S.xi u s -
      I * e * S.A u s * S.r u s * S.phi u s
  let G := fun s => source s - I * e * S.A u s * wV s
  have hGc : ContinuousOn G (Icc v u) :=
    hsc.sub (((Complex.continuous_ofReal.comp_continuousOn hAc).const_mul (I * e)).mul hVc)
  have hform : IntegralForm wU G v u :=
    ⟨hGc.intervalIntegrable_of_Icc hvu,
      (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hvu hwc hd
        (hGc.intervalIntegrable_of_Icc hvu)).symm⟩
  have hb : wU u = -(S.phi u u - H + S.xi u u / S.nu u u) / 2 := by
    dsimp only [wU]
    rw [hRL, hstar, hA, hnu]
    push_cast
    field_simp
    ring
  apply Observation.incoming_transfer_of_source_envelope hvu hrho hR hlam hrad hspeed hRL
    (mul_nonneg hCn (add_nonneg hNp hNm))
    (mul_nonneg (add_nonneg hCe (mul_nonneg hCp hBv)) heta) hform hb
  intro s hs
  have hrp : 0 < S.r u s := hrho.trans_le (hrad s hs).1
  have hLp : 0 < L := hrp.trans_le (hrad s hs).2
  have hnorm : ‖I * e * S.A u s * wV s‖ = |e * S.A u s| * ‖wV s‖ := by
    simp only [norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul, one_mul]
  have hc : ‖I * e * S.A u s * wV s‖ ≤ Cp * eta / (L * S.r u s) * Bv := by
    rw [hnorm]
    exact mul_le_mul (hpotential s hs) (hV s hs) (norm_nonneg _) (by positivity)
  have hn := (norm_sub_le (source s) (I * e * S.A u s * wV s)).trans
    (add_le_add (hsource s hs) hc)
  have hextra : 0 ≤ Cp * Bv * eta / (S.r u s) ^ 4 := by positivity
  change ‖G s‖ ≤ _
  dsimp only [G]
  apply hn.trans
  have heq : Cn * (Nphi + Nm) / (S.r u s) ^ 3 +
      (Ce + Cp * Bv) * eta / (S.r u s) ^ 4 +
      (Ce + Cp * Bv) * eta / (L * S.r u s) =
      (Cn * (Nphi + Nm) / (S.r u s) ^ 3 +
        Ce * (eta / (S.r u s) ^ 4 + eta / (L * S.r u s)) +
        Cp * eta / (L * S.r u s) * Bv) + Cp * Bv * eta / (S.r u s) ^ 4 := by ring
  rw [heq]
  exact le_add_of_nonneg_right hextra

/-- [internal]
Raw normalized outer-chart data, in the exact interface of the outer
comparison theorem, with the additional outgoing equations for `nu,xi`.
This record contains geometry, component equations, static data and
original boundary data only. It contains no comparison, source envelope,
charge improvement, trace estimate or continuation conclusion. -/
structure Observation.OuterNormalizationData
    (Kstatic Ct Bboundary : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
    (H P : ℂ) (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
    (a b Lzero L epsilon eta qStar e : ℝ) : Prop where
  /-- Ordered radial interval. -/
  ordered : Lzero ≤ L
  /-- Boundary and electric errors in the normalized source range. -/
  errors : epsilon ∈ Icc 0 1 ∧ eta ∈ Icc 0 1
  /-- Reference charge normalization. -/
  reference_charge : |qStar| ≤ 1
  /-- Physical charged-size identity, retaining the scalar background. -/
  scale : |e| * L * (1 + ‖H‖) = eta
  /-- Compactness of the actual sideways truncation. -/
  compact : IsCompact (sidewaysTruncation S D a b Lzero L)
  /-- Continuity of the eight fields used in the outer comparison. -/
  fields :
    let R := sidewaysTruncation S D a b Lzero L
    ContinuousOn (Function.uncurry S.r) R ∧ ContinuousOn (Function.uncurry S.nu) R ∧
      ContinuousOn (Function.uncurry S.lam) R ∧ ContinuousOn (Function.uncurry S.A) R ∧
      ContinuousOn (Function.uncurry S.phi) R ∧ ContinuousOn (Function.uncurry S.theta) R ∧
      ContinuousOn (Function.uncurry S.m) R ∧ ContinuousOn (Function.uncurry S.Q) R
  /-- Continuity of the additional incoming scalar field. -/
  incoming_continuous : ContinuousOn (Function.uncurry S.xi)
    (sidewaysTruncation S D a b Lzero L)
  /-- AC radial static mass. -/
  static_mass_ac : AbsolutelyContinuousOnInterval mStar Lzero L
  /-- Continuous radial static scalar and ratio. -/
  static_continuous : ContinuousOn phiStar (Icc Lzero L) ∧ ContinuousOn yStar (Icc Lzero L)
  /-- Exact static endpoint scalar data. -/
  static_boundary : phiStar L = P / (L : ℂ) ∧ phiStar L + yStar L = 0
  /-- The three static radial equations. -/
  static_equations :
    let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
    ∀ s ∈ Icc Lzero L,
      HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r) (phiStar s + yStar s) s ∧
      HasDerivAt (fun r => phiStar r + yStar r) ((-ks s / s : ℝ) * yStar s) s ∧
      HasDerivAt mStar
        ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s
  /-- Uniform static outer bounds. -/
  static_bounds : ∀ s ∈ Icc Lzero L,
    |mStar s| ≤ 2 ∧ ‖yStar s‖ ≤ Kstatic / s ∧ |1 - 2 * mStar s / s| ≤ 2 ∧
      ‖(s : ℂ) * phiStar s‖ ≤ Kstatic ∧ ‖phiStar s + yStar s‖ ≤ Kstatic / s ^ 2 ∧
        1 / 2 ≤ 1 - 2 * mStar s / s
  /-- Nonempty outer cylinder in the same region. -/
  base : ∃ p ∈ sidewaysTruncation S D a b Lzero L, S.r p.1 p.2 = L
  /-- Every characteristic dependence triangle stays in the same region. -/
  triangles : ∀ p ∈ sidewaysTruncation S D a b Lzero L,
    sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b Lzero L
  /-- Optical, mass and gap bounds supplied by normalization. -/
  box : ∀ p ∈ sidewaysTruncation S D a b Lzero L,
    S.nu p.1 p.2 ∈ Icc (-(1 / 2)) (-(1 / 8)) ∧
      S.lam p.1 p.2 ∈ Icc (1 / 8) (1 / 2) ∧ S.m p.1 p.2 ∈ Icc 0 2 ∧
        1 / 2 ≤ 1 - S.mu p.1 p.2
  /-- Normalized characteristic component equations used by the outer packet. -/
  equations : ∀ p ∈ sidewaysTruncation S D a b Lzero L,
    HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1 ∧
      HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧
      HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2 ∧
      HasDerivAt (S.phi p.1) (S.phiV p.1 p.2) p.2 ∧
      HasDerivAt (S.Q p.1) (S.QV e p.1 p.2) p.2 ∧
      HasDerivAt (S.A p.1) (S.AV p.1 p.2) p.2 ∧
      HasDerivAt (fun u => S.lam u p.2) (S.rUV p.1 p.2) p.1 ∧
      HasDerivAt (fun u => S.phi u p.2) (S.phiU e p.1 p.2) p.1 ∧
      HasDerivAt (fun u => S.theta u p.2) (S.thetaU e p.1 p.2) p.1
  /-- The outgoing expansion and incoming-scalar equations. -/
  incoming_equations : ∀ p ∈ sidewaysTruncation S D a b Lzero L,
    HasDerivAt (S.nu p.1) (S.rUV p.1 p.2) p.2 ∧
      HasDerivAt (S.xi p.1) (S.xiV e p.1 p.2) p.2
  /-- Original normalized boundary data, before any outer improvement. -/
  boundary : ∀ t, (t, t) ∈ sidewaysTruncation S D a b Lzero L →
    S.r t t = L ∧ S.lam t t = 1 / 2 ∧
      ‖S.phi t t - H - P / (L : ℂ)‖ ≤ Ct * epsilon / L ∧
      ‖S.a t t - H‖ ≤ epsilon / L ∧
      |massComparison S mStar t t| ≤ Ct * epsilon / L ∧ S.A t t = 0 ∧
      |S.Q t t - qStar| ≤ Bboundary * eta
  /-- Incoming expansion on the normalized outer cylinder. -/
  incoming_boundary : ∀ t, (t, t) ∈ sidewaysTruncation S D a b Lzero L →
    S.nu t t = -1 / 2

/-- [internal]
Discharge the outer source, charge, potential and outgoing transport
inputs from raw normalized data and the two literal outer comparison
norm bounds. The potential and neutral constants depend only on
`Kstatic`; the electric and charge constants are selected after the
fixed boundary charge coefficient, before all comparison data. -/
theorem Observation.incoming_transfer_of_raw_outer_estimates
    (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Cp Cn : ℝ, 0 < Cp ∧ 0 < Cn ∧
    ∀ Bboundary : ℝ, 0 ≤ Bboundary → ∃ Ce Cq : ℝ, 0 < Ce ∧ 0 < Cq ∧
    ∀ (Ct : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ)
      (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b Lzero L epsilon eta qStar e Nphi Nm : ℝ),
    let R := sidewaysTruncation S D a b Lzero L
    Observation.OuterNormalizationData Kstatic Ct Bboundary S D H P phiStar yStar mStar
      a b Lzero L epsilon eta qStar e →
    1 ≤ Lzero → 0 ≤ Ct → Cq * eta ≤ 1 → 0 ≤ Nphi → Nphi ≤ 1 → 0 ≤ Nm →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal Nphi →
    comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal Nm →
    (∀ p ∈ R, |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r p.1 p.2)) ∧
    ∀ p ∈ R,
      ‖((S.nu p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H -
        (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2))) + S.xi p.1 p.2 -
          I * e * S.A p.1 p.2 * S.r p.1 p.2 * S.phi p.1 p.2) +
        (S.phi p.1 p.1 - H + S.xi p.1 p.1 / S.nu p.1 p.1) / 2‖ ≤
        Cn * (Nphi + Nm) / S.r p.1 p.2 ^ 2 + Ce * eta / S.r p.1 p.2 ^ 3 +
          Ce * eta / L * Real.log (L / S.r p.1 p.2) := by
  obtain ⟨Cp, hCp, hpotentialConstants⟩ :=
    Observation.outer_charge_potential_of_normalization Kstatic hKs
  obtain ⟨_CpS, Cn, _hCpS, hCn, hsourceConstants⟩ :=
    Observation.outer_sources_of_normalization Kstatic hKs
  refine ⟨Cp, 8 * Cn, hCp, by positivity, ?_⟩
  intro Bboundary hB
  obtain ⟨CqP, hCqP, hpotential⟩ := hpotentialConstants Bboundary hB
  obtain ⟨CqS, Ce, hCqS, hCe, hsource⟩ := hsourceConstants Bboundary hB
  let Bv := 1 + 40 * Cn + 16 * Ce
  refine ⟨8 * (Ce + Cp * Bv), max CqP CqS, by dsimp [Bv]; positivity,
    lt_of_lt_of_le hCqP (le_max_left _ _), ?_⟩
  intro Ct S D H P phiStar yStar mStar a b Lzero L epsilon eta qStar e Nphi Nm
  dsimp only
  intro h hLzero hCt hsmall hNp hstop hNm hw hmBound
  let R := sidewaysTruncation S D a b Lzero L
  let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  let k := fun u v => (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
  let wV := fun u v => (S.lam u v : ℂ) *
    (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v
  let source := fun u v =>
    -(((-S.nu u v) * S.lam u v * k u v / S.r u v ^ 2 : ℝ) : ℂ) *
      scalarComparison S H phiStar u v +
    (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) * yStar (S.r u v) *
      ((k u v - ks (S.r u v) : ℝ) : ℂ) -
    I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) *
      (H + (phiStar (S.r u v) + yStar (S.r u v))) +
    I * ((e * (-S.nu u v) * S.lam u v * S.Q u v /
      ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
      (shiftedRphi S H u v + (S.r u v : ℂ) * H)
  rcases h.fields with ⟨hr, hnu, hlam, hA, hphi, htheta, hm, hQ⟩
  have hLp : 0 < Lzero := zero_lt_one.trans_le hLzero
  have hL : 1 ≤ L := hLzero.trans h.ordered
  have hPsmall : CqP * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) h.errors.2.1).trans hsmall
  have hSsmall : CqS * eta ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) h.errors.2.1).trans hsmall
  have hstopNorm : comparisonNorm R (scalarComparison S H phiStar) ≤ 1 := by
    apply hw.trans
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hstop
  have hsec {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :=
    continuousOn_outgoing_of_subtriangle hc (h.triangles p hp)
  have hstat (p) (hp : p ∈ R) := h.static_bounds (S.r p.1 p.2) hp.2
  have hbox (p) (hp : p ∈ R) : 0 < S.lam p.1 p.2 ∧ |S.nu p.1 p.2| ≤ 1 / 2 ∧
      S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2 := by
    have hb := h.box p hp
    exact ⟨(by norm_num : (0 : ℝ) < 1 / 8).trans_le hb.2.1.1,
      abs_le.mpr ⟨hb.1.1, by linarith only [hb.1.2]⟩, hb.2.2⟩
  have hdout (p) (hp : p ∈ R) (t) (ht : t ∈ Ioo p.2 p.1) :=
    h.equations (p.1, t) ((sidewaysTruncation_paths (h.triangles p hp)).2 t
      (Ioo_subset_Icc_self ht))
  have hpot := hpotential S D e eta a b Lzero L qStar H phiStar hLp hL h.reference_charge
    h.scale hPsmall hstopNorm (fun p hp => (hstat p hp).2.2.2.1) h.triangles
    hr hlam hnu hm hQ hA hphi htheta hbox
    (fun p hp t ht => ⟨(hdout p hp t ht).2.1, (hdout p hp t ht).2.2.2.1,
      (hdout p hp t ht).2.2.2.2.1, (hdout p hp t ht).2.2.1,
      (hdout p hp t ht).2.2.2.2.2.1⟩)
    (fun t ht => ⟨(h.boundary t ht).1, (h.boundary t ht).2.2.2.2.2.1,
      (h.boundary t ht).2.2.2.2.2.2⟩)
  have hmass4 (p) (hp : p ∈ R) : ‖massComparison S mStar p.1 p.2‖ ≤ 4 := by
    change ‖S.m p.1 p.2 - mStar (S.r p.1 p.2)‖ ≤ 4
    apply (norm_sub_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg (h.box p hp).2.2.1.1, Real.norm_eq_abs]
    linarith only [(h.box p hp).2.2.1.2, (hstat p hp).1]
  have hsources (P M : ℝ) (hP : 0 ≤ P) (hP1 : P ≤ 1) (hM : 0 ≤ M)
      (hwP : ∀ p ∈ R, ‖scalarComparison S H phiStar p.1 p.2‖ ≤ P)
      (hmM : ∀ p ∈ R, ‖massComparison S mStar p.1 p.2‖ ≤ M) :=
    hsource S D e eta a b Lzero L qStar P M H phiStar yStar mStar hLzero h.ordered
      h.errors.2.1 h.reference_charge h.scale hSsmall hP hP1 hM hwP hmM
      (fun p hp => ⟨(hstat p hp).2.2.2.1, (hstat p hp).2.1,
        (hstat p hp).2.2.2.2.1, (hstat p hp).2.2.2.2.2⟩)
      h.triangles hr hlam hnu hm hQ hA hphi htheta
      (fun p hp => ⟨(hbox p hp).1, (h.box p hp).2.1.2,
        ⟨(h.box p hp).1.1, (h.box p hp).1.2.trans (by norm_num)⟩, (h.box p hp).2.2⟩)
      (fun p hp t ht => ⟨(hdout p hp t ht).2.1, (hdout p hp t ht).2.2.2.1,
        (hdout p hp t ht).2.2.2.2.1, (hdout p hp t ht).2.2.1,
        (hdout p hp t ht).2.2.2.2.2.1⟩)
      (fun t ht => ⟨(h.boundary t ht).1, (h.boundary t ht).2.2.2.2.2.1,
        (h.boundary t ht).2.2.2.2.2.2⟩)
  have hsActual := hsources Nphi Nm hNp hstop hNm
    (fun p hp => norm_le_of_comparisonNorm_le hNp hp hw)
    (fun p hp => norm_le_of_comparisonNorm_le hNm hp hmBound)
  have hsCoarse := hsources 1 4 (by norm_num) le_rfl (by norm_num)
    (fun p hp => norm_le_of_comparisonNorm_le (by norm_num) hp
      (by simpa only [ENNReal.ofReal_one] using hstopNorm)) hmass4
  have hmsc : ContinuousOn mStar (Icc Lzero L) := by
    simpa only [uIcc_of_le h.ordered] using h.static_mass_ac.continuousOn
  have hks : ContinuousOn ks (Icc Lzero L) := by
    have hc : ContinuousOn (fun s => 2 * mStar s / s) (Icc Lzero L) :=
      (continuousOn_const.mul hmsc).div continuousOn_id (fun s hs => (hLp.trans_le hs.1).ne')
    exact (hc.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hLp.trans_le hs.1).ne'))).div (continuousOn_const.sub hc)
      (fun s hs => by linarith only [(h.static_bounds s hs).2.2.2.2.2])
  have hsectionIn {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :
      ContinuousOn (fun u => f u p.2) (Icc p.2 p.1) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => h.triangles p hp (sidewaysTriangle_incoming hu))
  have htransport (p) (hp : p ∈ R) := co_wv_transport_of_normalization H phiStar yStar ks
    hp.1.2.2.1 (hsectionIn hr p hp) (hsectionIn hnu p hp) (hsectionIn hlam p hp)
    (hsectionIn hm p hp) (hsectionIn hQ p hp) (hsectionIn hA p hp)
    (hsectionIn hphi p hp) (hsectionIn htheta p hp)
    (fun u hu => (hLp.trans_le (h.triangles p hp (sidewaysTriangle_incoming hu)).2.1).ne')
    (fun u hu => by linarith only [(h.box (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming hu))).2.2.2])
    (h.static_continuous.1.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (h.static_continuous.2.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (hks.mono (by
      rintro r ⟨u, hu, rfl⟩
      exact (h.triangles p hp (sidewaysTriangle_incoming hu)).2))
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.2.1)
    (fun u hu => (h.equations (u, p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu)))).2.2.2.2.2.2.2.2)
    (fun u hu => (h.static_equations (S.r u p.2)
      (h.triangles p hp (sidewaysTriangle_incoming (Ioo_subset_Icc_self hu))).2).2.1)
  have hV (p) (hp : p ∈ R) : ‖wV p.1 p.2‖ ≤ Bv := by
    have ht := htransport p hp
    have hboundary := h.boundary p.2 (h.triangles p hp
      (sidewaysTriangle_incoming ⟨le_rfl, hp.1.2.2.1⟩))
    have hb := Observation.outer_boundary_difference_data_of_normalization S H P phiStar yStar
      (hLp.trans_le h.ordered) hboundary.1 hboundary.2.1 h.static_boundary.1 h.static_boundary.2
      hboundary.2.2.1 hboundary.2.2.2.1
    apply Observation.outgoing_derivative_uniform_of_outer (hLzero.trans hp.2.1) hp.2.2
      hCn.le hCe.le (by norm_num) le_rfl (by norm_num) le_rfl h.errors.1.2 h.errors.2.1 h.errors.2.2
    apply incoming_comparison_bound hp.1.2.2.1 hLp
      (fun u hu => (h.equations (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).1)
      (hsectionIn hnu p hp) (fun u hu => (h.triangles p hp (sidewaysTriangle_incoming hu)).2)
      (fun u hu => (h.box (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).1.2)
      hboundary.1 (by positivity : 0 ≤ Cn * (1 + 4)) (mul_nonneg hCe.le h.errors.2.1)
      ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2
    · simpa only [wV, hb.2.1] using hb.2.2
    · intro u hu
      convert (hsCoarse (u, p.2) (h.triangles p hp (sidewaysTriangle_incoming hu))).2.2 using 1
      ring
  refine ⟨fun p hp => (hpot p hp).2.2.2, ?_⟩
  intro p hp
  have hpath := (sidewaysTruncation_paths (h.triangles p hp)).2
  have hpr := h.static_continuous.1.comp (hsec hr p hp) (fun t ht => (hpath t ht).2)
  have hyr := h.static_continuous.2.comp (hsec hr p hp) (fun t ht => (hpath t ht).2)
  have hrc := Complex.continuous_ofReal.comp_continuousOn (hsec hr p hp)
  have hwc := (((Complex.continuous_ofReal.comp_continuousOn (hsec hnu p hp)).mul
    (((hsec hphi p hp).sub (continuousOn_const (c := H))).sub
      (hpr.add hyr))).add
      (hsec h.incoming_continuous p hp)).sub
        ((((Complex.continuous_ofReal.comp_continuousOn (hsec hA p hp)).const_mul (I * e)).mul
          hrc).mul
          (hsec hphi p hp))
  have hVc := ((Complex.continuous_ofReal.comp_continuousOn (hsec hlam p hp)).mul
    (((hsec hphi p hp).sub (continuousOn_const (c := H))).sub (hpr.add hyr))).add (hsec htheta p hp)
  have hsc : ContinuousOn (source p.1) (Icc p.2 p.1) := by
    have cr := hsec hr p hp
    have cn := hsec hnu p hp
    have cl := hsec hlam p hp
    have cm := hsec hm p hp
    have cq := hsec hQ p hp
    have ca := hsec hA p hp
    have cf := hsec hphi p hp
    have cks := hks.comp cr (fun s hs => (hpath s hs).2)
    have hr0 (s) (hs : s ∈ Icc p.2 p.1) := (hLp.trans_le (hpath s hs).2.1).ne'
    have hg0 (s) (hs : s ∈ Icc p.2 p.1) : 1 - S.mu p.1 s ≠ 0 := by
      linarith only [(h.box (p.1, s) (hpath s hs)).2.2.2]
    have cmu : ContinuousOn (fun s => S.mu p.1 s) (Icc p.2 p.1) :=
      (continuousOn_const.mul cm).div cr hr0
    have ck : ContinuousOn (k p.1) (Icc p.2 p.1) :=
      (cmu.sub ((cq.pow 2).div (cr.pow 2) (fun s hs => pow_ne_zero 2 (hr0 s hs)))).div
        (continuousOn_const.sub cmu) hg0
    have lift {f : ℝ → ℝ} (hc : ContinuousOn f (Icc p.2 p.1)) :=
      Complex.continuous_ofReal.comp_continuousOn hc
    have cpsi := (lift cr).mul (cf.sub (continuousOn_const (c := H)))
    have cw := cpsi.sub ((lift cr).mul hpr)
    have c1 := ((cn.neg.mul cl).mul ck).div (cr.pow 2) (fun s hs => pow_ne_zero 2 (hr0 s hs))
    have c2 := (cn.neg.mul cl).div cr hr0
    have c3 := (ca.const_mul e).mul cl
    have c4 := ((((cn.neg.const_mul e).mul cl).mul cq).div
      ((continuousOn_const.sub cmu).mul (cr.pow 2)))
      (fun s hs => mul_ne_zero (hg0 s hs) (pow_ne_zero 2 (hr0 s hs)))
    exact ((((lift c1).neg.mul cw).add (((lift c2).mul hyr).mul (lift (ck.sub cks)))).sub
      (((lift c3).const_mul I).mul (continuousOn_const.add (hpr.add hyr)))).add
      (((lift c4).const_mul I).mul (cpsi.add ((lift cr).mul continuousOn_const)))
  refine (Observation.incoming_derivative_transfer_of_outer (Bv := Bv)
    H phiStar yStar (wV p.1) (source p.1)
    hp.1.2.2.1 hLp hCn.le hCe.le hCp.le (by dsimp [Bv]; positivity) hNp hNm h.errors.2.1
    (fun s hs => (h.equations (p.1, s) (hpath s hs)).2.1) (hsec hlam p hp) (hsec hA p hp)
    hVc hsc (fun s hs => (hpath s hs).2)
    (fun s hs => (h.box (p.1, s) (hpath s hs)).2.1.1)
    (h.boundary p.1 (hpath p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
    (h.incoming_boundary p.1 (hpath p.1 ⟨hp.1.2.2.1, le_rfl⟩))
    (h.boundary p.1 (hpath p.1 ⟨hp.1.2.2.1, le_rfl⟩)).2.2.2.2.2.1 h.static_boundary.2 hwc
    ?_ ?_ ?_ ?_).trans_eq (by ring)
  · intro s hs
    have hp' := hpath s (Ioo_subset_Icc_self hs)
    convert Observation.incoming_mixed_deriv_of_normalization H phiStar yStar
      (hLp.trans_le hp'.2.1).ne' (h.equations (p.1, s) hp').2.1
      (h.incoming_equations (p.1, s) hp').1 (h.equations (p.1, s) hp').2.2.2.1
      (h.incoming_equations (p.1, s) hp').2 (h.equations (p.1, s) hp').2.2.2.2.2.1
      (h.static_equations (S.r p.1 s) hp'.2).2.1 using 1
    dsimp only [source, wV, k, ks]
    push_cast
    ring
  · intro s hs
    exact (hsActual (p.1, s) (hpath s hs)).2.2
  · intro s hs
    have hh := (hpot (p.1, s) (hpath s hs)).2.2.2
    have hn := mul_nonneg (abs_nonneg (e * S.A p.1 s)) (norm_nonneg H)
    linarith only [hh, hn]
  · intro s hs
    exact hV (p.1, s) (hpath s hs)

end EmcsfAcExtension.Global
