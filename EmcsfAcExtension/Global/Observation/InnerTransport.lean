module

public import EmcsfAcExtension.Global.Api.Definitions
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Global.Observation.OuterMass
import EmcsfAcExtension.Infra.LinearTransport
import EmcsfAcExtension.Global.Observation.InnerMass
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Exact scalar difference transports on the inner annulus

Only characteristic derivatives already present in the frozen equations
are used. The neutral radial reference is differentiated covariantly in
the incoming equation, retaining the resulting potential source.
Source: charged_SF_new_version.tex:L2610–L2643; internal project record (Iy) and (Iz).
-/

public section

open Complex Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [node eq:co-inner-y]
The incoming outgoing-ratio difference equation in ordinary derivative
form. Adding `I * e * A * Y` gives precisely the source covariant
equation. In particular the reference contributes `-I * e * A * yStar`.
The hypotheses are the radius, expansion and wave equations and the
radial static reference equation; there are no comparison estimates or
smallness assumptions. This form applies directly to transported null
equations, without a transformed regular-axis assertion. -/
theorem co_inner_y
    (S : Fields) (e : ℝ) (yStar : ℝ → ℂ) (kStar : ℝ → ℝ) {u v : ℝ}
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hg : 1 - S.mu u v ≠ 0)
    (hdr : HasDerivAt (fun x => S.r x v) (S.nu u v) u)
    (hdl : HasDerivAt (fun x => S.lam x v) (S.rUV u v) u)
    (hdt : HasDerivAt (fun x => S.theta x v) (S.thetaU e u v) u)
    (hdy : HasDerivAt yStar
      (((-(1 + kStar (S.r u v)) / S.r u v : ℝ) : ℂ) * yStar (S.r u v)) (S.r u v)) :
    let r := S.r u v
    let y := S.theta u v / (S.lam u v : ℂ)
    let z := S.xi u v / (S.nu u v : ℂ)
    let ys := yStar r
    let k : ℝ := (S.mu u v - S.Q u v ^ 2 / r ^ 2) / (1 - S.mu u v)
    HasDerivAt (fun x => S.theta x v / (S.lam x v : ℂ) - yStar (S.r x v))
      (((-S.nu u v / r : ℝ) : ℂ) * (z - ys + k * (y - ys)) +
        ((-S.nu u v / r * (k - kStar r) : ℝ) : ℂ) * ys +
        I * e * (-S.nu u v) * S.Q u v * S.phi u v / ((1 - S.mu u v) * r : ℝ) -
        I * e * S.A u v * ys - I * e * S.A u v * (y - ys)) u := by
  have hd := (hdt.div hdl.ofReal_comp (Complex.ofReal_ne_zero.mpr hl)).sub (hdy.scomp u hdr)
  dsimp only [Fields.thetaU, Fields.waveSource, Fields.rUV] at hd
  simp only [real_smul] at hd
  convert hd using 1
  · funext x
    simp only [Pi.div_apply, Pi.sub_apply, Function.comp_apply]
  · have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
    have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hgC : (1 : ℂ) - S.mu u v ≠ 0 := by exact_mod_cast hg
    push_cast
    field_simp [hrC, hlC, hnC, hgC]; ring

/-- [node eq:co-inner-z]
The outgoing incoming-ratio difference equation. There is no connection
term in this direction because the retained gauge has `A_V = 0`.
Only the outgoing derivatives of `xi` and `nu` are used; incoming
regularity of the incoming scalar ratio is not assumed. No constants or
smallness hypotheses enter this identity. -/
theorem co_inner_z
    (S : Fields) (e : ℝ) (yStar : ℝ → ℂ) (kStar : ℝ → ℝ) {u v : ℝ}
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hg : 1 - S.mu u v ≠ 0)
    (hdr : HasDerivAt (S.r u) (S.lam u v) v)
    (hdn : HasDerivAt (S.nu u) (S.rUV u v) v)
    (hdx : HasDerivAt (S.xi u) (S.xiV e u v) v)
    (hdy : HasDerivAt yStar
      (((-(1 + kStar (S.r u v)) / S.r u v : ℝ) : ℂ) * yStar (S.r u v)) (S.r u v)) :
    let r := S.r u v
    let y := S.theta u v / (S.lam u v : ℂ)
    let z := S.xi u v / (S.nu u v : ℂ)
    let ys := yStar r
    let k : ℝ := (S.mu u v - S.Q u v ^ 2 / r ^ 2) / (1 - S.mu u v)
    HasDerivAt (fun x => S.xi u x / (S.nu u x : ℂ) - yStar (S.r u x))
      (((-S.lam u v / r : ℝ) : ℂ) * (y - ys + k * (z - ys)) -
        ((S.lam u v / r * (k - kStar r) : ℝ) : ℂ) * ys +
        I * e * S.lam u v * S.Q u v * S.phi u v / ((1 - S.mu u v) * r : ℝ)) v := by
  have hd := (hdx.div hdn.ofReal_comp (Complex.ofReal_ne_zero.mpr hn)).sub (hdy.scomp v hdr)
  dsimp only [Fields.xiV, Fields.waveSource, Fields.rUV] at hd
  simp only [real_smul] at hd
  convert hd using 1
  · funext x
    simp only [Pi.div_apply, Pi.sub_apply, Function.comp_apply]
  · have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hlC : (S.lam u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
    have hnC : (S.nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    have hgC : (1 : ℂ) - S.mu u v ≠ 0 := by exact_mod_cast hg
    push_cast
    field_simp [hrC, hnC, hlC, hgC]; ring

/-- [internal]
The geometric rational difference on a fixed gap. The two exact
coefficients depend only on `delta,R`, uniformly in all four rational
arguments and the two error envelopes. -/
theorem Observation.inner_rational_difference_bound
    {mu muStar q qStar delta R M E : ℝ} (hdelta : 0 < delta)
    (hg : delta ≤ 1 - mu) (hgs : delta ≤ 1 - muStar)
    (hq : |qStar| ≤ R) (hm : |mu - muStar| ≤ M) (he : |q - qStar| ≤ E) :
    |(mu - q) / (1 - mu) - (muStar - qStar) / (1 - muStar)| ≤
      M * (1 + R) / delta ^ 2 + E / delta := by
  have hgp : 0 < 1 - mu := hdelta.trans_le hg
  have hgsp : 0 < 1 - muStar := hdelta.trans_le hgs
  have hM : 0 ≤ M := (abs_nonneg _).trans hm
  have hE : 0 ≤ E := (abs_nonneg _).trans he
  have hR : 0 ≤ R := (abs_nonneg _).trans hq
  have hden : delta ^ 2 ≤ (1 - mu) * (1 - muStar) := by
    simpa only [pow_two] using mul_le_mul hg hgs hdelta.le hgp.le
  have hq' : |1 - qStar| ≤ 1 + R := by
    exact (abs_sub _ _).trans (by rw [abs_one]; linarith only [hq])
  rw [geometric_coefficient_difference hgp.ne' hgsp.ne']
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hgp hgsp)]
    exact (div_le_div_of_nonneg_right (mul_le_mul hm hq' (abs_nonneg _) hM)
      (mul_pos hgp hgsp).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hM (by positivity)) (sq_pos_of_pos hdelta) hden)
  · rw [abs_div, abs_of_pos hgp]
    exact (div_le_div_of_nonneg_right he hgp.le).trans
      (div_le_div_of_nonneg_left hE hdelta hg)

/-- [internal]
The geometric source on the fixed positive-radius annulus is bounded
linearly by the literal mass error and electric error. The constants
are fixed after `rStar,delta,Qmax,B` alone, before the radius and actual
or reference fields; there is no dependence on the outer radius,
background or coupling. The same estimate permits negative reference
mass and is uniform over the stopped reference family. -/
theorem Observation.inner_geometric_source_bound
    (rStar delta Qmax B : ℝ) (hrStar : 0 < rStar) (hdelta : 0 < delta)
    (hQmax : 0 ≤ Qmax) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ r m mStar Q qStar eta : ℝ,
      rStar ≤ r → 0 ≤ eta → delta ≤ 1 - 2 * m / r →
      delta ≤ 1 - 2 * mStar / r → |Q| ≤ Qmax → |qStar| ≤ Qmax →
      |Q - qStar| ≤ B * eta →
      |(2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r) -
        (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)| ≤
          C * (|m - mStar| + eta) := by
  let CM := 2 / rStar * (1 + Qmax ^ 2 / rStar ^ 2) / delta ^ 2
  let CE := 2 * Qmax * B / rStar ^ 2 / delta
  let C := CM + CE + 1
  have hCM : 0 ≤ CM := by dsimp [CM]; positivity
  have hCE : 0 ≤ CE := by dsimp [CE]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r m mStar Q qStar eta hr heta hg hgs hQ hq hcharge
  have hrp : 0 < r := hrStar.trans_le hr
  have hmu : |2 * m / r - 2 * mStar / r| ≤ 2 / rStar * |m - mStar| := by
    rw [show 2 * m / r - 2 * mStar / r = 2 * (m - mStar) / r by ring,
      abs_div, abs_mul, abs_of_pos hrp, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (abs_nonneg _)) hrStar hr).trans_eq
      (by ring)
  have hq2 : qStar ^ 2 ≤ Qmax ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hQmax).mpr hq
  have hqfrac : |qStar ^ 2 / r ^ 2| ≤ Qmax ^ 2 / rStar ^ 2 := by
    rw [abs_of_nonneg (by positivity : 0 ≤ qStar ^ 2 / r ^ 2)]
    exact (div_le_div_of_nonneg_right hq2 (sq_nonneg r)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hrStar)
        (pow_le_pow_left₀ hrStar.le hr 2))
  have hcharge2 : |Q ^ 2 - qStar ^ 2| ≤ 2 * Qmax * B * eta := by
    rw [show Q ^ 2 - qStar ^ 2 = (Q - qStar) * (Q + qStar) by ring, abs_mul]
    have hsum : |Q + qStar| ≤ 2 * Qmax :=
      (abs_add_le _ _).trans (by linarith only [hQ, hq])
    exact (mul_le_mul hcharge hsum (abs_nonneg _) (mul_nonneg hB heta)).trans_eq (by ring)
  have hqdiff : |Q ^ 2 / r ^ 2 - qStar ^ 2 / r ^ 2| ≤
      (2 * Qmax * B / rStar ^ 2) * eta := by
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hrp)]
    exact ((div_le_div_of_nonneg_right hcharge2 (sq_nonneg r)).trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hrStar)
        (pow_le_pow_left₀ hrStar.le hr 2))).trans_eq (by ring)
  have h := Observation.inner_rational_difference_bound hdelta hg hgs hqfrac hmu hqdiff
  have hm0 := abs_nonneg (m - mStar)
  have hextra := mul_nonneg hCE hm0
  have hextra' := mul_nonneg hCM heta
  have h' : _ ≤ CM * |m - mStar| + CE * eta := h.trans_eq (by dsimp [CM, CE]; ring)
  apply h'.trans
  dsimp only [C]
  nlinarith only [hextra, hextra', hm0, heta]

/-- [internal]
Both charged sources in the inner scalar transports are uniformly small.
The constant depends only on the fixed positive lower radius, gap,
charge, scalar, reference and retained-potential bounds. It is selected
before the physical scale, background, coupling and pointwise values.
The potential term is retained, including the reference scalar ratio. -/
theorem Observation.inner_charged_source_bound
    (rStar delta Qmax Cscalar Kstatic Amax : ℝ)
    (hrStar : 0 < rStar) (hdelta : 0 < delta) (hQmax : 0 ≤ Qmax)
    (hCs : 0 ≤ Cscalar) (hKs : 0 ≤ Kstatic) (hAmax : 0 ≤ Amax) :
    ∃ C > 0, ∀ (r L g Q e eta A : ℝ) (H phi yStar : ℂ),
      rStar ≤ r → 1 ≤ L → delta ≤ g → 0 ≤ eta → |Q| ≤ Qmax →
      ‖phi‖ ≤ ‖H‖ + Cscalar → ‖yStar‖ ≤ Kstatic →
      |e| * L * (1 + ‖H‖) ≤ eta → |e * A| * (1 + ‖H‖) ≤ Amax * eta →
      ‖I * e * Q * phi / (g * r : ℝ)‖ + ‖I * e * A * yStar‖ ≤ C * eta := by
  let CQ := (Cscalar + 1) * Qmax / (delta * rStar)
  let CA := Amax * Kstatic
  let C := CQ + CA + 1
  have hCQ : 0 ≤ CQ := by dsimp [CQ]; positivity
  have hCA : 0 ≤ CA := mul_nonneg hAmax hKs
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r L g Q e eta A H phi yStar hr hL hg heta hQ hphi hys hscale hpotential
  have hrp : 0 < r := hrStar.trans_le hr
  have hgp : 0 < g := hdelta.trans_le hg
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : |e| * (1 + ‖H‖) ≤ eta / L := by
    apply (le_div_iff₀ hLp).mpr
    convert hscale using 1
    ring
  have hphib : ‖phi‖ ≤ (Cscalar + 1) * (1 + ‖H‖) := by
    have hh := mul_nonneg hCs (norm_nonneg H)
    nlinarith only [hphi, hh]
  have hdiv : eta / L ≤ eta := (div_le_self heta hL)
  have hep : |e| * ‖phi‖ ≤ (Cscalar + 1) * eta := by
    calc
      _ ≤ |e| * ((Cscalar + 1) * (1 + ‖H‖)) :=
        mul_le_mul_of_nonneg_left hphib (abs_nonneg _)
      _ = (Cscalar + 1) * (|e| * (1 + ‖H‖)) := by ring
      _ ≤ (Cscalar + 1) * (eta / L) := mul_le_mul_of_nonneg_left he (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by positivity)
  have ha : |e * A| ≤ Amax * eta := by
    have hh := mul_nonneg (abs_nonneg (e * A)) (norm_nonneg H)
    nlinarith only [hpotential, hh]
  have hfirst : ‖I * e * Q * phi / (g * r : ℝ)‖ ≤ CQ * eta := by
    have hnorm : ‖I * e * Q * phi / (g * r : ℝ)‖ =
        (|e| * ‖phi‖) * |Q| / (g * r) := by
      simp only [norm_div, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
        one_mul, abs_of_pos hgp, abs_of_pos hrp]
      ring
    rw [hnorm]
    have hn := mul_le_mul hep hQ (abs_nonneg _) (by positivity : 0 ≤ (Cscalar + 1) * eta)
    have hd : delta * rStar ≤ g * r := mul_le_mul hg hr hrStar.le hgp.le
    exact ((div_le_div_of_nonneg_right hn (mul_pos hgp hrp).le).trans
      (div_le_div_of_nonneg_left (by positivity) (mul_pos hdelta hrStar) hd)).trans_eq
      (by dsimp [CQ]; ring)
  have hsecond : ‖I * e * A * yStar‖ ≤ CA * eta := by
    have hnorm : ‖I * e * A * yStar‖ = |e * A| * ‖yStar‖ := by
      simp only [norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul, one_mul]
    rw [hnorm]
    exact (mul_le_mul ha hys (norm_nonneg _) (mul_nonneg hAmax heta)).trans_eq
      (by dsimp [CA]; ring)
  dsimp only [C]
  nlinarith only [hfirst, hsecond, heta]

/-- [internal]
Backward radial transport retains the incoming boundary value at exactly
the same outgoing label. The coefficient depends only on the displayed
coefficient bounds `A,B` and maximum radius `Lzero`, before every field,
boundary trace, depth and electric error. The source envelope is supplied
by the preceding inner source bounds. The equation is an ordinary
outgoing characteristic equation, with no incoming derivative of `Z`. -/
theorem Observation.inner_incoming_transport_of_source_bounds
    (A B Lzero : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hLzero : 0 ≤ Lzero) :
    ∃ C > 0, ∀ (Z source : ℝ → ℂ) (a F N : ℝ → ℝ) (r eta : ℝ),
      0 ≤ r → r ≤ Lzero → 0 ≤ eta →
      ContinuousOn Z (Icc r Lzero) → ContinuousOn source (Icc r Lzero) →
      ContinuousOn a (Icc r Lzero) →
      ContinuousOn F (Icc 0 (Lzero - r)) → ContinuousOn N (Icc 0 (Lzero - r)) →
      (∀ s ∈ Icc 0 (Lzero - r), 0 ≤ F s ∧ 0 ≤ N s) →
      (∀ s ∈ Icc r Lzero, a s ≤ A) →
      (∀ s ∈ Ioo r Lzero, HasDerivAt Z (-(a s : ℂ) * Z s + source s) s) →
      (∀ s ∈ Icc r Lzero, ‖source s‖ ≤ B * (F (Lzero - s) + N (Lzero - s) + eta)) →
      ‖Z r‖ ≤ C * ‖Z Lzero‖ + C * eta +
        C * ∫ s in 0..(Lzero - r), F s + N s := by
  let E := Real.exp (A * Lzero)
  let C := E * (B * (Lzero + 1) + 1)
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  have hCE : E ≤ C := by
    have hp := mul_nonneg hE.le (mul_nonneg hB (by positivity : 0 ≤ Lzero + 1))
    dsimp only [C]
    nlinarith only [hp]
  have hCB : E * B ≤ C := by
    have hp := mul_nonneg (mul_nonneg hE.le hB) hLzero
    dsimp only [C]
    nlinarith only [hp, hE.le]
  have hCBL : E * B * Lzero ≤ C := by
    have hp := mul_nonneg hE.le hB
    dsimp only [C]
    nlinarith only [hp, hE.le]
  refine ⟨C, hC, ?_⟩
  intro Z source a F N r eta hr hrL heta hZ hs ha hF hN hnonneg hcoeff hd hsource
  have hdepth : 0 ≤ Lzero - r := sub_nonneg.mpr hrL
  have hmap (s : ℝ) (hs : s ∈ Icc r Lzero) : Lzero - s ∈ Icc 0 (Lzero - r) :=
    ⟨sub_nonneg.mpr hs.2, sub_le_sub_left hs.1 Lzero⟩
  have hderc : ContinuousOn (fun s => -(a s : ℂ) * Z s + source s) (Icc r Lzero) :=
    (((Complex.continuous_ofReal.comp_continuousOn ha).neg).mul hZ).add hs
  have hac : AbsolutelyContinuousOnInterval Z r Lzero := by
    apply absolutelyContinuousOnInterval_of_integralForm_on
      (g := fun s => -(a s : ℂ) * Z s + source s) hrL
    intro s ht
    have hsub : Icc r s ⊆ Icc r Lzero := Icc_subset_Icc le_rfl ht.2
    have hi := (hderc.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hZ.mono hsub) (fun t ht' => hd t ⟨ht'.1, ht'.2.trans_le ht.2⟩) hi).symm⟩
  have heq : ∀ᵐ s ∂volume.restrict (Icc r Lzero),
      deriv Z s = -(a s : ℂ) * Z s + source s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s ht => (hd s ht).deriv)
  have hfactor := Observation.inner_backward_factor_bound hr hrL hA ha hcoeff
  have hback := Observation.backward_complex_norm_le hrL hac
    (ha.intervalIntegrable_of_Icc hrL) (hs.intervalIntegrable_of_Icc hrL) heq hfactor
  have hFNc : ContinuousOn (fun s => F (Lzero - s) + N (Lzero - s)) (Icc r Lzero) :=
    (hF.add hN).comp (continuous_const.sub continuous_id).continuousOn hmap
  have hsubst : (∫ s in r..Lzero, F (Lzero - s) + N (Lzero - s)) =
      ∫ s in 0..(Lzero - r), F s + N s := by
    simpa only [sub_self] using
      intervalIntegral.integral_comp_sub_left (fun s => F s + N s) Lzero (a := r) (b := Lzero)
  have hi := intervalIntegral.integral_mono_on hrL
    (hs.norm.intervalIntegrable_of_Icc (μ := volume) hrL)
    ((hFNc.add continuousOn_const).intervalIntegrable_of_Icc (μ := volume) hrL |>.const_mul B)
    hsource
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_add (hFNc.intervalIntegrable_of_Icc (μ := volume) hrL)
      intervalIntegrable_const, hsubst, intervalIntegral.integral_const, smul_eq_mul] at hi
  have hI : 0 ≤ ∫ s in 0..(Lzero - r), F s + N s :=
    intervalIntegral.integral_nonneg hdepth (fun s ht =>
      add_nonneg (hnonneg s ht).1 (hnonneg s ht).2)
  have herror := mul_nonneg (mul_nonneg hE.le hB) (mul_nonneg heta hr)
  have hsource' := mul_le_mul_of_nonneg_left hi hE.le
  have hboundary := mul_le_mul_of_nonneg_right hCE (norm_nonneg (Z Lzero))
  have helectric := mul_le_mul_of_nonneg_right hCBL heta
  have hintegral := mul_le_mul_of_nonneg_right hCB hI
  change ‖Z r‖ ≤ E * (‖Z Lzero‖ + ∫ s in r..Lzero, ‖source s‖) at hback
  linarith only [hback, hsource', herror, hboundary, helectric, hintegral]

/-- [internal]
The inner radial-depth substitution has its exact characteristic
Jacobian. The coefficient is one, uniformly in the depth profile,
window and weight; no lower speed or inverse coordinate is needed. -/
theorem Observation.inner_depth_integral
    {depth w f : ℝ → ℝ} {a b d : ℝ} (hab : a ≤ b)
    (hd : ∀ s ∈ Icc a b, HasDerivAt depth (w s) s)
    (cw : ContinuousOn w (Icc a b)) (cf : ContinuousOn f (Icc 0 d))
    (hmem : ∀ s ∈ Icc a b, depth s ∈ Icc 0 d)
    (ha : depth a = 0) (hb : depth b = d) :
    (∫ s in a..b, w s * f (depth s)) = ∫ t in 0..d, f t := by
  have hi := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b)
    (fun s hs => hd s (by simpa only [uIcc_of_le hab] using hs))
    (by simpa only [uIcc_of_le hab] using cw)
    (cf.mono (by
      rintro _ ⟨s, hs, rfl⟩
      exact hmem s (by simpa only [uIcc_of_le hab] using hs)))
  rw [ha, hb] at hi
  simpa only [mul_comm, Function.comp_apply] using hi

/-- [internal]
Integrate the outgoing scalar difference covariantly on one incoming
section, using the same-label incoming boundary error in L². The exact
coefficients depend only on `B,Cz`, before all functions and errors.
The only trace input is its full boundary square integral; the real
connection is treated by its unitary integrating factor. -/
theorem Observation.inner_scalar_ray_of_source_bounds
    (B Cz : ℝ) (hB : 0 ≤ B) (hCz : 0 ≤ Cz)
    {Y Z source h : ℝ → ℂ} {connection depth w F N : ℝ → ℝ}
    {a₀ a b b₀ d eta etheta exi : ℝ}
    (haa : a₀ ≤ a) (hab : a ≤ b) (hbb : b ≤ b₀)
    (hd0 : 0 ≤ d) (_heta : 0 ≤ eta) (hexi : 0 ≤ exi)
    (cY : ContinuousOn Y (Icc a b)) (cG : ContinuousOn source (Icc a b))
    (cB : ContinuousOn connection (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (ch : ContinuousOn h (Icc a₀ b₀)) (cF : ContinuousOn F (Icc 0 d))
    (cN : ContinuousOn N (Icc 0 d))
    (hdepth : ∀ s ∈ Icc a b, HasDerivAt depth (w s) s)
    (hmem : ∀ s ∈ Icc a b, depth s ∈ Icc 0 d)
    (ha : depth a = 0) (hb : depth b = d)
    (hw : ∀ s ∈ Icc a b, 0 ≤ w s ∧ w s ≤ 1 / 2)
    (_hfn : ∀ s ∈ Icc 0 d, 0 ≤ F s ∧ 0 ≤ N s)
    (htrace : (∫ s in a₀..b₀, ‖h s‖ ^ 2) ≤ exi ^ 2)
    (hboundary : ‖Y a‖ ≤ etheta)
    (hdY : ∀ s ∈ Ioo a b,
      HasDerivAt Y (-I * (connection s : ℂ) * Y s + source s) s)
    (hZ : ∀ s ∈ Icc a b, ‖Z s‖ ≤ Cz * ‖h s‖ + Cz * eta +
      Cz * ∫ t in 0..depth s, F t + N t)
    (hsource : ∀ s ∈ Icc a b, ‖source s‖ ≤
      w s * B * (‖Z s‖ + F (depth s) + N (depth s) + eta)) :
    ‖Y b‖ ≤ etheta + B * Cz * (Real.sqrt (d / 2) * exi) + B * (Cz + 1) * eta * d +
      B * Cz * (∫ s in 0..d, ∫ t in 0..s, F t + N t) + B * ∫ s in 0..d, F s + N s := by
  have cd : ContinuousOn depth (Icc a b) :=
    fun s hs => (hdepth s hs).continuousAt.continuousWithinAt
  have cFN : ContinuousOn (fun s => F s + N s) (Icc 0 d) := cF.add cN
  have iFN := cFN.intervalIntegrable_of_Icc (μ := volume) hd0
  let J := fun s => ∫ t in 0..s, F t + N t
  have cJ : ContinuousOn J (Icc 0 d) := by
    simpa only [uIcc_of_le hd0] using
      (iFN.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).continuousOn
  have cHd := ch.mono (Icc_subset_Icc haa hbb)
  have cJd := cJ.comp cd hmem
  have cFNd := cFN.comp cd hmem
  have iw := cw.intervalIntegrable_of_Icc (μ := volume) hab
  have iH := (cw.mul cHd.norm).intervalIntegrable_of_Icc (μ := volume) hab
  have iJ := (cw.mul cJd).intervalIntegrable_of_Icc (μ := volume) hab
  have iW := (cw.mul cFNd).intervalIntegrable_of_Icc (μ := volume) hab
  have hwd : (∫ s in a..b, w s) = d := by
    simpa only [mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      Observation.inner_depth_integral hab hdepth cw
        (continuousOn_const (c := (1 : ℝ))) hmem ha hb
  have hWI := Observation.inner_depth_integral hab hdepth cw cFN hmem ha hb
  have hJI := Observation.inner_depth_integral hab hdepth cw cJ hmem ha hb
  have hHI := Observation.inner_l2_boundary_integral haa hab hbb ch cw
    (fun s hs => (hw s hs).1) (fun s hs => (hw s hs).2) hwd hexi htrace
  have hlin (s : ℝ) (hs : s ∈ Icc a b) : ‖source s‖ ≤
      B * Cz * (w s * ‖h s‖) + (B * (Cz + 1) * eta) * w s +
        B * Cz * (w s * J (depth s)) + B * (w s * (F (depth s) + N (depth s))) := by
    have hz := mul_le_mul_of_nonneg_left (hZ s hs) (mul_nonneg (hw s hs).1 hB)
    dsimp only [J]
    nlinarith only [hsource s hs, hz]
  have hi := intervalIntegral.integral_mono_on hab
    (cG.norm.intervalIntegrable_of_Icc (μ := volume) hab)
    ((((iH.const_mul (B * Cz)).add (iw.const_mul (B * (Cz + 1) * eta))).add
      (iJ.const_mul (B * Cz))).add (iW.const_mul B)) hlin
  rw [intervalIntegral.integral_add
      (((iH.const_mul (B * Cz)).add (iw.const_mul (B * (Cz + 1) * eta))).add
        (iJ.const_mul (B * Cz)))
      (iW.const_mul B),
    intervalIntegral.integral_add ((iH.const_mul (B * Cz)).add
      (iw.const_mul (B * (Cz + 1) * eta))) (iJ.const_mul (B * Cz)),
    intervalIntegral.integral_add (iH.const_mul (B * Cz))
      (iw.const_mul (B * (Cz + 1) * eta)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hwd] at hi
  simp only [Pi.mul_apply, Function.comp_apply] at hi
  rw [hWI, hJI] at hi
  have chder : ContinuousOn (fun s => -I * (connection s : ℂ) * Y s + source s) (Icc a b) :=
    (((Complex.continuous_ofReal.comp_continuousOn cB).const_mul (-I)).mul cY).add cG
  have hac : AbsolutelyContinuousOnInterval Y a b := by
    apply absolutelyContinuousOnInterval_of_integralForm_on
      (g := fun s => -I * (connection s : ℂ) * Y s + source s) hab
    intro s hs
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hs.2
    have hI := (chder.mono hsub).intervalIntegrable_of_Icc (μ := volume) hs.1
    exact ⟨hI, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 (cY.mono hsub)
      (fun t ht => hdY t ⟨ht.1, ht.2.trans_le hs.2⟩) hI).symm⟩
  have heq : ∀ᵐ s ∂volume.restrict (Icc a b),
      deriv Y s = -I * (connection s : ℂ) * Y s + source s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => (hdY s hs).deriv)
  have ht := unitary_transport_norm_le hab hac (cB.intervalIntegrable_of_Icc hab)
    (cG.intervalIntegrable_of_Icc hab) heq
  have hh := mul_le_mul_of_nonneg_left hHI (mul_nonneg hB hCz)
  linarith only [ht, hboundary, hi, hh]

/-- [internal]
The normalized fixed-annulus comparison setting, with primitive
scalar/charge/potential bounds from the preceding normalization nodes.
Only outgoing scalar and mass boundary errors are uniform; the incoming
boundary datum is supplied solely by its full squared clock integral.
No inner comparison estimate, transport envelope or Volterra bound is
a field of this record. -/
structure Observation.InnerComparisonData
    (rho Lzero delta c K G Qmax Cscalar Bcharge Amax : ℝ)
    (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ) (yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
    (a b qStar e eta etheta em exi : ℝ) : Prop where
  /-- Closed normalized boundary clock window, possibly a singleton. -/
  ordered : a ≤ b
  /-- Nonnegative electric and boundary error parameters. -/
  errors : 0 ≤ eta ∧ 0 ≤ etheta ∧ 0 ≤ em ∧ 0 ≤ exi
  /-- Compact complete inner comparison region. -/
  compact : IsCompact (sidewaysTruncation S D a b rho Lzero)
  /-- Every normalized boundary clock value represents an actual point. -/
  boundary_mem : ∀ t ∈ Icc a b, (t, t) ∈ sidewaysTruncation S D a b rho Lzero
  /-- Every required characteristic triangle stays in the same region. -/
  triangles : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
    sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b rho Lzero
  /-- Continuous representatives of all nine fields. -/
  fields :
    let R := sidewaysTruncation S D a b rho Lzero
    ContinuousOn (Function.uncurry S.r) R ∧ ContinuousOn (Function.uncurry S.nu) R ∧
    ContinuousOn (Function.uncurry S.lam) R ∧ ContinuousOn (Function.uncurry S.A) R ∧
    ContinuousOn (Function.uncurry S.phi) R ∧ ContinuousOn (Function.uncurry S.theta) R ∧
    ContinuousOn (Function.uncurry S.m) R ∧ ContinuousOn (Function.uncurry S.Q) R ∧
    ContinuousOn (Function.uncurry S.xi) R
  /-- Fixed annular optical, mass and gap bounds. -/
  box : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
    -S.nu p.1 p.2 ∈ Icc c (1 / 2) ∧ S.lam p.1 p.2 ∈ Icc c (1 / 2) ∧
    S.m p.1 p.2 ∈ Icc 0 2 ∧ delta ≤ 1 - S.mu p.1 p.2
  /-- Primitive fixed-annulus scalar, charge and potential controls. -/
  charged : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
    ‖S.phi p.1 p.2‖ ≤ ‖H‖ + Cscalar ∧ |S.Q p.1 p.2| ≤ Qmax ∧
    |S.Q p.1 p.2 - qStar| ≤ Bcharge * eta ∧
    |e * S.A p.1 p.2| * (1 + ‖H‖) ≤ Amax * eta
  /-- Physical coupling size after the outer normalization. -/
  scale : |e| * (1 + ‖H‖) ≤ eta
  /-- Fixed normalized reference charge bound. -/
  reference_charge : |qStar| ≤ Qmax
  /-- Continuous stopped reference scalar and mass. -/
  static_continuous : ContinuousOn yStar (Icc rho Lzero) ∧
    ContinuousOn mStar (Icc rho Lzero)
  /-- Uniform stopped reference ratio, gap and mass-factor bounds. -/
  static_bounds : ∀ s ∈ Icc rho Lzero,
    ‖yStar s‖ ≤ K ∧ delta ≤ 1 - 2 * mStar s / s ∧ |1 - 2 * mStar s / s| ≤ G
  /-- The two exact static radial equations. -/
  static_equations :
    let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
    ∀ s ∈ Ioo rho Lzero,
      HasDerivAt yStar (((-(1 + ks s) / s : ℝ) : ℂ) * yStar s) s ∧
      HasDerivAt mStar
        ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s
  /-- Characteristic component equations, with no transformed axis assertion. -/
  equations : ∀ p ∈ sidewaysTruncation S D a b rho Lzero,
    HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1 ∧
    HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧
    HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2 ∧
    HasDerivAt (fun u => S.lam u p.2) (S.rUV p.1 p.2) p.1 ∧
    HasDerivAt (fun u => S.theta u p.2) (S.thetaU e p.1 p.2) p.1 ∧
    HasDerivAt (S.nu p.1) (S.rUV p.1 p.2) p.2 ∧
    HasDerivAt (S.xi p.1) (S.xiV e p.1 p.2) p.2
  /-- Exact inner cylinder and the two uniform outgoing boundary errors. -/
  boundary : ∀ t ∈ Icc a b, S.r t t = Lzero ∧
    ‖S.theta t t / (S.lam t t : ℂ) - yStar Lzero‖ ≤ etheta ∧
    |S.m t t - mStar Lzero| ≤ em
  /-- Incoming boundary error only in the clock L² measure. -/
  trace : (∫ t in a..b, ‖S.xi t t / (S.nu t t : ℂ) - yStar Lzero‖ ^ 2) ≤ exi ^ 2

/-- [internal]
The two exact scalar sources have a common linear envelope. Its explicit
coefficient depends only on `Ar,Ak,Ad,Ce,Cp,c`, before all scalar values,
mass/electric errors and optical weights. The retained potential is
converted to radial measure using the positive lower expansion `c`. -/
theorem Observation.inner_linear_source_norms
    {Ar Ak Ad Ce Cp c : ℝ} (hAr : 0 ≤ Ar) (hAk : 0 ≤ Ak) (hAd : 0 ≤ Ad)
    (hCe : 0 ≤ Ce) (hCp : 0 ≤ Cp) (hc : 0 < c)
    {w a k b M eta : ℝ} {Y Z ys electric potential : ℂ}
    (hw : c ≤ w) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (ha : |a| ≤ Ar) (hk : |k| ≤ Ak) (hb : ‖(b : ℂ) * ys‖ ≤ Ad * (M + eta))
    (he : ‖electric‖ ≤ Ce * eta) (hp : ‖potential‖ ≤ Cp * eta) :
    let B := Ar + Ak + Ad + Ce + Cp / c
    ‖-(a : ℂ) * Y - (b : ℂ) * ys + electric‖ ≤ B * (‖Y‖ + M + eta) ∧
    ‖(w : ℂ) * ((a : ℂ) * Z + (k : ℂ) * Y + (b : ℂ) * ys + electric) - potential‖ ≤
      w * B * (‖Z‖ + ‖Y‖ + M + eta) := by
  have hw0 : 0 ≤ w := (hc.trans_le hw).le
  have haY : ‖-(a : ℂ) * Y‖ ≤ Ar * ‖Y‖ := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have haZ : ‖(a : ℂ) * Z‖ ≤ Ar * ‖Z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
  have hkY : ‖(k : ℂ) * Y‖ ≤ Ak * ‖Y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  have hz : ‖-(a : ℂ) * Y - (b : ℂ) * ys + electric‖ ≤
      Ar * ‖Y‖ + Ad * (M + eta) + Ce * eta := (norm_add_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add haY hb)) he)
  have hy : ‖(w : ℂ) * ((a : ℂ) * Z + (k : ℂ) * Y + (b : ℂ) * ys + electric) - potential‖ ≤
      ‖(w : ℂ) * ((a : ℂ) * Z + (k : ℂ) * Y + (b : ℂ) * ys + electric)‖ + Cp * eta :=
    (norm_sub_le _ potential).trans (add_le_add le_rfl hp)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0] at hy
  have hsum : ‖(a : ℂ) * Z + (k : ℂ) * Y + (b : ℂ) * ys + electric‖ ≤
      Ar * ‖Z‖ + Ak * ‖Y‖ + Ad * (M + eta) + Ce * eta := (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add haZ hkY)) hb)) he)
  have hZsum : Ar * ‖Y‖ + Ad * (M + eta) + Ce * eta ≤
      (Ar + Ad + Ce) * (‖Y‖ + M + eta) := by
    have h1 := mul_le_mul_of_nonneg_left (show ‖Y‖ ≤ ‖Y‖ + M + eta by linarith) hAr
    have h2 := mul_le_mul_of_nonneg_left
      (show M + eta ≤ ‖Y‖ + M + eta by linarith only [norm_nonneg Y]) hAd
    have h3 := mul_le_mul_of_nonneg_left
      (show eta ≤ ‖Y‖ + M + eta by linarith only [norm_nonneg Y, hM]) hCe
    linarith only [h1, h2, h3]
  constructor
  · have hh : 0 ≤ (Ak + Cp / c) * (‖Y‖ + M + eta) := by positivity
    nlinarith only [hz, hZsum, hh]
  · have hYsum : Ar * ‖Z‖ + Ak * ‖Y‖ + Ad * (M + eta) + Ce * eta ≤
        (Ar + Ak + Ad + Ce) * (‖Z‖ + ‖Y‖ + M + eta) := by
      have h1 := mul_le_mul_of_nonneg_left
        (show ‖Z‖ ≤ ‖Z‖ + ‖Y‖ + M + eta by linarith only [norm_nonneg Y, hM, heta]) hAr
      have h2 := mul_le_mul_of_nonneg_left
        (show ‖Y‖ ≤ ‖Z‖ + ‖Y‖ + M + eta by linarith only [norm_nonneg Z, hM, heta]) hAk
      have h3 := mul_le_mul_of_nonneg_left
        (show M + eta ≤ ‖Z‖ + ‖Y‖ + M + eta by linarith only [norm_nonneg Y, norm_nonneg Z]) hAd
      have h4 := mul_le_mul_of_nonneg_left
        (show eta ≤ ‖Z‖ + ‖Y‖ + M + eta by linarith only [norm_nonneg Y, norm_nonneg Z, hM]) hCe
      linarith only [h1, h2, h3, h4]
    have hpw : Cp ≤ w * (Cp / c) := by
      calc
        Cp = c * (Cp / c) := by field_simp [hc.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_right hw (div_nonneg hCp hc.le)
    have hpot := mul_le_mul hpw
      (show eta ≤ ‖Z‖ + ‖Y‖ + M + eta by linarith only [norm_nonneg Y, norm_nonneg Z, hM])
      heta (by positivity : 0 ≤ w * (Cp / c))
    have hs := mul_le_mul_of_nonneg_left (hsum.trans hYsum) hw0
    nlinarith only [hy, hs, hpot]

end EmcsfAcExtension.Global
