module

public import EmcsfAcExtension.Global.Observation.Potential
public import EmcsfAcExtension.Frozen.Fields.RadiusUV
public import EmcsfAcExtension.Frozen.Fields.PhiU
public import EmcsfAcExtension.Frozen.Fields.ThetaU
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Exact shifted wave and comparison equations

The scalar background is retained in every charged term. Normalization
supplies the individual field equations on the actual characteristic
sections; no frozen solution predicate is asserted in the cylinder chart.
Source: `charged_SF_new_version.tex:L2407–L2461`, approved internal project record (W) and (K).
-/

public section

open Set MeasureTheory Complex Filter Topology

namespace EmcsfAcExtension.Global

/-- [internal]
The outgoing derivative of the literal shifted scalar, using only the two
normalized outgoing radius and scalar equations. -/
theorem shifted_rphi_out_deriv_of_normalization
    {S : Fields} {H : ℂ} {u v : ℝ} (hr : S.r u v ≠ 0)
    (hR : HasDerivAt (S.r u) (S.lam u v) v)
    (hphi : HasDerivAt (S.phi u) (S.theta u v / (S.r u v : ℂ)) v) :
    HasDerivAt (shiftedRphi S H u)
      ((S.lam u v : ℂ) * (S.phi u v - H) + S.theta u v) v := by
  convert hR.ofReal_comp.mul (hphi.sub_const H) using 1
  · rfl
  · field_simp [Complex.ofReal_ne_zero.mpr hr]

/-- [internal]
The exact incoming derivative of the outgoing shifted scalar derivative.
There are no constants or smallness assumptions. The three derivative
hypotheses are precisely the normalized radius, scalar and wave equations.
Every term containing the retained background `H` is present. -/
theorem co_shifted_wave_of_normalization
    {S : Fields} {e u v : ℝ} (H : ℂ)
    (hr : S.r u v ≠ 0) (_hg : 1 - S.mu u v ≠ 0)
    (hlam : HasDerivAt (fun s => S.lam s v) (S.rUV u v) u)
    (hphi : HasDerivAt (fun s => S.phi s v) (S.phiU e u v) u)
    (htheta : HasDerivAt (fun s => S.theta s v) (S.thetaU e u v) u) :
    HasDerivAt (fun s => (S.lam s v : ℂ) * (S.phi s v - H) + S.theta s v)
      (-(((-S.nu u v) * S.lam u v / S.r u v ^ 2 *
            ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) : ℝ) : ℂ) *
          shiftedRphi S H u v -
        I * e * S.A u v *
          ((S.lam u v : ℂ) * (S.phi u v - H) + S.theta u v + S.lam u v * H) +
        I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v : ℝ) * S.r u v ^ 2 : ℝ) *
          (shiftedRphi S H u v + S.r u v * H)) u := by
  convert (hlam.ofReal_comp.mul (hphi.sub_const H)).add htheta using 1
  dsimp only [Fields.rUV, Fields.phiU, Fields.thetaU, Fields.waveSource, shiftedRphi]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hr]
  ring

/-- [internal]
The exact comparison equation, in ordinary derivative form with the
connection term displayed on the right. The static input is the radial
equation `f'' = -kStar*yStar/r` for `f = r*phiStar`, with
`f' = phiStar+yStar`. There are no estimates or discarded background terms.
Normalization supplies just the four incoming field equations. -/
theorem co_wv_exact_of_normalization
    {S : Fields} {e u v kStar : ℝ} (H : ℂ) (phiStar yStar : ℝ → ℂ)
    (hr : S.r u v ≠ 0)
    (hR : HasDerivAt (fun s => S.r s v) (S.nu u v) u)
    (hlam : HasDerivAt (fun s => S.lam s v) (S.rUV u v) u)
    (hphi : HasDerivAt (fun s => S.phi s v) (S.phiU e u v) u)
    (htheta : HasDerivAt (fun s => S.theta s v) (S.thetaU e u v) u)
    (hstatic : HasDerivAt (fun r => phiStar r + yStar r)
      ((-kStar / S.r u v : ℝ) * yStar (S.r u v)) (S.r u v)) :
    let k := (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
    let wV := fun s => (S.lam s v : ℂ) *
      (S.phi s v - H - (phiStar (S.r s v) + yStar (S.r s v))) + S.theta s v
    HasDerivAt wV
      (-(((-S.nu u v) * S.lam u v * k / S.r u v ^ 2 : ℝ) : ℂ) *
          scalarComparison S H phiStar u v +
        (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) *
          yStar (S.r u v) * (k - kStar) -
        I * e * S.A u v * S.lam u v *
          (H + (phiStar (S.r u v) + yStar (S.r u v))) +
        I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v : ℝ) * S.r u v ^ 2 : ℝ) *
          (shiftedRphi S H u v + S.r u v * H) -
        I * e * S.A u v * wV u) u := by
  convert (hlam.ofReal_comp.mul
    ((hphi.sub_const H).sub (hstatic.scomp u hR))).add htheta using 1
  · rfl
  · dsimp only [Fields.rUV, Fields.phiU, Fields.thetaU, Fields.waveSource,
      scalarComparison, shiftedRphi, Pi.sub_apply, Function.comp_apply]
    simp only [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
    ring

/-- [internal]
The literal outgoing comparison derivative satisfies AC incoming transport.
The inputs are continuous normalized component fields on a closed proper
section, their incoming equations only at interior points, and the smooth
static radial equation `f'' = -kStar*yStar/r` with `f'=phiStar+yStar`.
Endpoint derivatives are not required: the FTC on each anchored subinterval
uses endpoint continuity, then gives absolute continuity. The connection
`B=e*A` is real, and every retained-background term occurs in the literal
source `F`. There are no constants or smallness hypotheses. -/
theorem co_wv_transport_of_normalization
    {S : Fields} {e v a b : ℝ} (H : ℂ) (phiStar yStar : ℝ → ℂ) (kStar : ℝ → ℝ)
    (hab : a ≤ b)
    (hrc : ContinuousOn (fun s => S.r s v) (Icc a b))
    (hnuc : ContinuousOn (fun s => S.nu s v) (Icc a b))
    (hlamc : ContinuousOn (fun s => S.lam s v) (Icc a b))
    (hmc : ContinuousOn (fun s => S.m s v) (Icc a b))
    (hQc : ContinuousOn (fun s => S.Q s v) (Icc a b))
    (hAc : ContinuousOn (fun s => S.A s v) (Icc a b))
    (hphic : ContinuousOn (fun s => S.phi s v) (Icc a b))
    (hthetac : ContinuousOn (fun s => S.theta s v) (Icc a b))
    (hr : ∀ s ∈ Icc a b, S.r s v ≠ 0)
    (hg : ∀ s ∈ Icc a b, 1 - S.mu s v ≠ 0)
    (hps : ContinuousOn phiStar ((fun s => S.r s v) '' Icc a b))
    (hys : ContinuousOn yStar ((fun s => S.r s v) '' Icc a b))
    (hks : ContinuousOn kStar ((fun s => S.r s v) '' Icc a b))
    (hR : ∀ s ∈ Ioo a b, HasDerivAt (fun s => S.r s v) (S.nu s v) s)
    (hlam : ∀ s ∈ Ioo a b, HasDerivAt (fun s => S.lam s v) (S.rUV s v) s)
    (hphi : ∀ s ∈ Ioo a b, HasDerivAt (fun s => S.phi s v) (S.phiU e s v) s)
    (htheta : ∀ s ∈ Ioo a b, HasDerivAt (fun s => S.theta s v) (S.thetaU e s v) s)
    (hstatic : ∀ s ∈ Ioo a b, HasDerivAt (fun r => phiStar r + yStar r)
      ((-kStar (S.r s v) / S.r s v : ℝ) * yStar (S.r s v)) (S.r s v)) :
    let k := fun s => (S.mu s v-S.Q s v^2/S.r s v^2)/(1-S.mu s v)
    let wV := fun s => (S.lam s v : ℂ)*
      (S.phi s v-H-(phiStar (S.r s v)+yStar (S.r s v)))+S.theta s v
    let B := fun s => e*S.A s v
    let F := fun s =>
      -(((-S.nu s v)*S.lam s v*k s/S.r s v^2 : ℝ) : ℂ)*scalarComparison S H phiStar s v +
      (((-S.nu s v)*S.lam s v/S.r s v : ℝ) : ℂ)*yStar (S.r s v)*
        ((k s-kStar (S.r s v) : ℝ) : ℂ) -
      I*((e*S.A s v*S.lam s v : ℝ) : ℂ)*(H+(phiStar (S.r s v)+yStar (S.r s v))) +
      I*((e*(-S.nu s v)*S.lam s v*S.Q s v/((1-S.mu s v)*S.r s v^2) : ℝ) : ℂ)*
        (shiftedRphi S H s v+(S.r s v : ℂ)*H)
    ContinuousOn wV (Icc a b) ∧ ContinuousOn B (Icc a b) ∧ ContinuousOn F (Icc a b) ∧
      AbsolutelyContinuousOnInterval wV a b ∧ IntervalIntegrable B volume a b ∧
      IntervalIntegrable F volume a b ∧
      (∀ᵐ s ∂volume.restrict (Icc a b), deriv wV s = -I*(B s : ℂ)*wV s+F s) := by
  dsimp only
  let k := fun s => (S.mu s v-S.Q s v^2/S.r s v^2)/(1-S.mu s v)
  let wV := fun s => (S.lam s v : ℂ)*
    (S.phi s v-H-(phiStar (S.r s v)+yStar (S.r s v)))+S.theta s v
  let B := fun s => e*S.A s v
  let F := fun s =>
    -(((-S.nu s v)*S.lam s v*k s/S.r s v^2 : ℝ) : ℂ)*scalarComparison S H phiStar s v +
    (((-S.nu s v)*S.lam s v/S.r s v : ℝ) : ℂ)*yStar (S.r s v)*
      ((k s-kStar (S.r s v) : ℝ) : ℂ) -
    I*((e*S.A s v*S.lam s v : ℝ) : ℂ)*(H+(phiStar (S.r s v)+yStar (S.r s v))) +
    I*((e*(-S.nu s v)*S.lam s v*S.Q s v/((1-S.mu s v)*S.r s v^2) : ℝ) : ℂ)*
      (shiftedRphi S H s v+(S.r s v : ℂ)*H)
  change ContinuousOn wV _ ∧ ContinuousOn B _ ∧ ContinuousOn F _ ∧
    AbsolutelyContinuousOnInterval wV _ _ ∧ IntervalIntegrable B _ _ _ ∧
    IntervalIntegrable F _ _ _ ∧ _
  have lift {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
      ContinuousOn (fun s => (f s : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn hf
  have hmuc : ContinuousOn (fun s => S.mu s v) (Icc a b) := by
    exact (continuousOn_const.mul hmc).div hrc hr
  have hkc : ContinuousOn k (Icc a b) :=
    (hmuc.sub ((hQc.pow 2).div (hrc.pow 2) (fun s hs => pow_ne_zero 2 (hr s hs)))).div
      (continuousOn_const.sub hmuc) hg
  have hpsr := hps.comp hrc (mapsTo_image _ _)
  have hysr := hys.comp hrc (mapsTo_image _ _)
  have hksr := hks.comp hrc (mapsTo_image _ _)
  have hwc : ContinuousOn wV (Icc a b) :=
    ((lift hlamc).mul ((hphic.sub continuousOn_const).sub (hpsr.add hysr))).add hthetac
  have hBc : ContinuousOn B (Icc a b) := hAc.const_mul e
  have hpsi : ContinuousOn (fun s => shiftedRphi S H s v) (Icc a b) :=
    (lift hrc).mul (hphic.sub continuousOn_const)
  have hw : ContinuousOn (fun s => scalarComparison S H phiStar s v) (Icc a b) :=
    hpsi.sub ((lift hrc).mul hpsr)
  have hc1 := ((hnuc.neg.mul hlamc).mul hkc).div (hrc.pow 2)
    (fun s hs => pow_ne_zero 2 (hr s hs))
  have hc2 := (hnuc.neg.mul hlamc).div hrc hr
  have hc3 := (hAc.const_mul e).mul hlamc
  have hc4 := ((((hnuc.neg.const_mul e).mul hlamc).mul hQc).div
    ((continuousOn_const.sub hmuc).mul (hrc.pow 2)))
    (fun s hs => mul_ne_zero (hg s hs) (pow_ne_zero 2 (hr s hs)))
  have hFc : ContinuousOn F (Icc a b) := by
    exact ((((lift hc1).neg.mul hw).add (((lift hc2).mul hysr).mul (lift (hkc.sub hksr)))).sub
      (((lift hc3).const_mul I).mul (continuousOn_const.add (hpsr.add hysr)))).add
      (((lift hc4).const_mul I).mul (hpsi.add ((lift hrc).mul continuousOn_const)))
  let G := fun s => -I*(B s : ℂ)*wV s+F s
  have hGc : ContinuousOn G (Icc a b) :=
    (((lift hBc).const_mul (-I)).mul hwc).add hFc
  have hd (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt wV (G s) s := by
    convert co_wv_exact_of_normalization H phiStar yStar
      (hr s (Ioo_subset_Icc_self hs)) (hR s hs) (hlam s hs) (hphi s hs) (htheta s hs)
      (hstatic s hs) using 1
    dsimp only [G, F, B, k, wV]
    push_cast
    ring
  have hform (x : ℝ) (hx : x ∈ Icc a b) : IntegralForm wV G a x := by
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hi : IntervalIntegrable G volume a x := (hGc.mono hsub).intervalIntegrable_of_Icc hx.1
    exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hwc.mono hsub)
      (fun s hs => hd s ⟨hs.1, hs.2.trans_le hx.2⟩) hi).symm⟩
  refine ⟨hwc, hBc, hFc, absolutelyContinuousOnInterval_of_integralForm_on hab hform,
    hBc.intervalIntegrable_of_Icc hab, hFc.intervalIntegrable_of_Icc hab, ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => (hd s hs).deriv)

/-- [internal]
The full pointwise source envelope for the exact wave comparison.
The neutral coefficient is chosen after the universal static bound `K`;
the electric coefficient is then chosen after the fixed universal potential
coefficient `Cp` and the boundary-charge coefficient `B`, before all solution data. Thus the former
is universal
and the latter depends only on the fixed window and gap. The potential,
charge and optical hypotheses are the previously proved normalization
conclusions. Here `a` denotes `(-nu)*lam`. -/
theorem co_source_envelope_of_normalization (K Cp : ℝ) (hK : 1 ≤ K) (hCp : 0 ≤ Cp) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ B : ℝ, 0 ≤ B →
      ∃ Ce : ℝ, 0 < Ce ∧
        ∀ (r L m mStar Q qStar e eta A a lam Nphi Nm : ℝ)
          (H psi w yStar fPrime : ℂ),
          1 ≤ r → 0 < L → 0 ≤ eta →
          |m| ≤ 2 → 1 / 2 ≤ 1 - 2 * m / r → 1 / 2 ≤ 1 - 2 * mStar / r →
          a ∈ Icc 0 1 → lam ∈ Icc 0 1 →
          |Q| ≤ 2 → |qStar| ≤ 1 → |Q - qStar| ≤ B * eta →
          |e| * L * (1 + ‖H‖) = eta →
          |e * A| * (1 + ‖H‖) ≤ Cp * eta / (L * r) →
          ‖w‖ ≤ Nphi → |m - mStar| ≤ Nm →
          ‖psi‖ ≤ K → ‖yStar‖ ≤ K / r → ‖fPrime‖ ≤ K / r ^ 2 →
          let k := (2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)
          let kStar : ℝ := (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)
          ‖-((a * k / r ^ 2 : ℝ) : ℂ) * w +
            ((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ) -
            I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime) +
            I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
              (psi + (r : ℂ) * H)‖ ≤
            Cn * (Nphi + Nm) / r ^ 3 + Ce * (eta / r ^ 4 + eta / (L * r)) := by
  refine ⟨16 * K, by positivity, fun B hB =>
    ⟨(6 * B + Cp + 4) * K, by positivity, ?_⟩⟩
  intro r L m mStar Q qStar e eta A a lam Nphi Nm H psi w yStar fPrime
    hr hL heta hm hg hgs ha hlam hQ hq hcharge hscale hpotential hw hmass hpsi hy hf
  let k := (2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)
  let kStar := (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hgp : 0 < 1 - 2 * m / r := by linarith only [hg]
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hNphi : 0 ≤ Nphi := (norm_nonneg _).trans hw
  have hNm : 0 ≤ Nm := (abs_nonneg _).trans hmass
  have hk : |k| ≤ 16 / r := outer_geometric_coefficient_bound hr hm hQ hg
  have hkk : |k - kStar| ≤ 16 * Nm / r + 6 * B * eta / r ^ 2 :=
    outer_geometric_difference_bound hr hg hgs hmass hQ hq hcharge
  have hfirst : ‖-((a * k / r ^ 2 : ℝ) : ℂ) * w‖ ≤ 16 * Nphi / r ^ 3 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_of_nonneg ha.1, abs_of_pos (sq_pos_of_pos hrp)]
    calc
      _ ≤ ((1 * (16 / r)) / r ^ 2) * Nphi := by gcongr; exact ha.2
      _ = _ := by ring
  have hsecond : ‖((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ)‖ ≤
      16 * K * Nm / r ^ 3 + 6 * K * B * eta / r ^ 4 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
      abs_of_nonneg ha.1, abs_of_pos hrp]
    calc
      _ ≤ (1 / r) * (K / r) * (16 * Nm / r + 6 * B * eta / r ^ 2) := by
        gcongr; exact ha.2
      _ = _ := by ring
  have hfK : ‖fPrime‖ ≤ K := by
    apply hf.trans
    apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
    have hr2 : 1 ≤ r ^ 2 := by nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr), hr]
    nlinarith only [mul_nonneg hK0 (sub_nonneg.mpr hr2)]
  have hHf : ‖H + fPrime‖ ≤ K * (1 + ‖H‖) := by
    apply (norm_add_le _ _).trans
    have hprod := mul_nonneg (sub_nonneg.mpr hK) (norm_nonneg H)
    nlinarith only [hfK, hprod]
  have hthird : ‖I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime)‖ ≤
      Cp * K * eta / (L * r) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hlam.1]
    calc
      _ ≤ |e * A| * 1 * (K * (1 + ‖H‖)) := by gcongr; exact hlam.2
      _ = K * (|e * A| * (1 + ‖H‖)) := by ring
      _ ≤ K * (Cp * eta / (L * r)) := mul_le_mul_of_nonneg_left hpotential hK0
      _ = _ := by ring
  have hcoeff : |e * a * Q / ((1 - 2 * m / r) * r ^ 2)| ≤ 4 * |e| / r ^ 2 := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg ha.1,
      abs_of_pos (mul_pos hgp (sq_pos_of_pos hrp))]
    apply (div_le_div_iff₀ (mul_pos hgp (sq_pos_of_pos hrp)) (sq_pos_of_pos hrp)).mpr
    have hnum : |e| * a * |Q| ≤ 2 * |e| := by
      calc
        _ ≤ |e| * 1 * 2 := by gcongr; exact ha.2
        _ = _ := by ring
    have hn := mul_le_mul_of_nonneg_right hnum (sq_nonneg r)
    have hg' := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4 * |e| * r ^ 2 by positivity)
    linear_combination hn + hg'
  have hpsiH : ‖psi + (r : ℂ) * H‖ ≤ K * r * (1 + ‖H‖) := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp]
    have hKr := mul_le_mul_of_nonneg_left hr hK0
    have hKH := mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hrp.le (norm_nonneg H))
    nlinarith only [hpsi, hKr, hKH]
  have hfourth : ‖I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
      (psi + (r : ℂ) * H)‖ ≤ 4 * K * eta / (L * r) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (4 * |e| / r ^ 2) * (K * r * (1 + ‖H‖)) :=
        mul_le_mul hcoeff hpsiH (norm_nonneg _) (by positivity)
      _ = 4 * K * eta / (L * r) := by rw [← hscale]; field_simp
  change ‖-((a * k / r ^ 2 : ℝ) : ℂ) * w +
      ((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ) -
      I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime) +
      I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
        (psi + (r : ℂ) * H)‖ ≤ _
  apply le_trans (b :=
    ‖-((a * k / r ^ 2 : ℝ) : ℂ) * w‖ +
    ‖((a / r : ℝ) : ℂ) * yStar * ((k - kStar : ℝ) : ℂ)‖ +
    ‖I * ((e * A * lam : ℝ) : ℂ) * (H + fPrime)‖ +
    ‖I * ((e * a * Q / ((1 - 2 * m / r) * r ^ 2) : ℝ) : ℂ) *
      (psi + (r : ℂ) * H)‖)
    ((norm_add_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl))
  apply (add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth).trans
  have hn := mul_nonneg (sub_nonneg.mpr hK) hNphi
  have he1 : 0 ≤ (Cp + 4) * K * eta / r ^ 4 := by positivity
  have he2 : 0 ≤ 6 * B * K * eta / (L * r) := by positivity
  linear_combination 16 / r ^ 3 * hn + he1 + he2

/-- [internal]
The conditional source and charge envelopes on the actual outer truncation,
derived from the raw normalized outgoing equations. The universal potential
and neutral coefficients are selected after `Kstatic` alone; the charge and
electric coefficients are then selected after the fixed boundary charge
coefficient. No source-envelope or improved-charge conclusion is assumed.
The scalar and mass inputs are the temporary literal pointwise sup bounds. -/
theorem Observation.outer_sources_of_normalization (Kstatic : ℝ) (hK : 0 ≤ Kstatic) :
    ∃ Cp Cn : ℝ, 0 < Cp ∧ 0 < Cn ∧
    ∀ Bboundary : ℝ, 0 ≤ Bboundary → ∃ Cq Ce : ℝ, 0 < Cq ∧ 0 < Ce ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (e eta a b rho L qStar Nphi Nm : ℝ)
      (H : ℂ) (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ),
    let K := sidewaysTruncation S D a b rho L
    let k := fun u v => (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
    let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
    let F := fun u v =>
      -(((-S.nu u v) * S.lam u v * k u v / S.r u v ^ 2 : ℝ) : ℂ) *
          scalarComparison S H phiStar u v +
      (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) * yStar (S.r u v) *
        ((k u v - ks (S.r u v) : ℝ) : ℂ) -
      I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) *
        (H + (phiStar (S.r u v) + yStar (S.r u v))) +
      I * ((e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
        (shiftedRphi S H u v + (S.r u v : ℂ) * H)
    1 ≤ rho → rho ≤ L → 0 ≤ eta → |qStar| ≤ 1 →
    |e| * L * (1 + ‖H‖) = eta → Cq * eta ≤ 1 →
    0 ≤ Nphi → Nphi ≤ 1 → 0 ≤ Nm →
    (∀ p ∈ K, ‖scalarComparison S H phiStar p.1 p.2‖ ≤ Nphi) →
    (∀ p ∈ K, ‖massComparison S mStar p.1 p.2‖ ≤ Nm) →
    (∀ p ∈ K,
      ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ ≤ Kstatic ∧
      ‖yStar (S.r p.1 p.2)‖ ≤ Kstatic / S.r p.1 p.2 ∧
      ‖phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2)‖ ≤ Kstatic / S.r p.1 p.2 ^ 2 ∧
      1 / 2 ≤ 1 - 2 * mStar (S.r p.1 p.2) / S.r p.1 p.2) →
    (∀ p ∈ K, sidewaysTriangle p.2 p.1 ⊆ K) →
    ContinuousOn (Function.uncurry S.r) K → ContinuousOn (Function.uncurry S.lam) K →
    ContinuousOn (Function.uncurry S.nu) K → ContinuousOn (Function.uncurry S.m) K →
    ContinuousOn (Function.uncurry S.Q) K → ContinuousOn (Function.uncurry S.A) K →
    ContinuousOn (Function.uncurry S.phi) K → ContinuousOn (Function.uncurry S.theta) K →
    (∀ p ∈ K, 0 < S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 / 2 ∧
      S.nu p.1 p.2 ∈ Icc (-(1 / 2)) 0 ∧
      S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2) →
    (∀ p ∈ K, ∀ t ∈ Ioo p.2 p.1,
      HasDerivAt (S.r p.1) (S.lam p.1 t) t ∧
      HasDerivAt (S.phi p.1) (S.phiV p.1 t) t ∧
      HasDerivAt (S.Q p.1) (S.QV e p.1 t) t ∧
      HasDerivAt (S.m p.1) (S.mV p.1 t) t ∧
      HasDerivAt (S.A p.1) (S.AV p.1 t) t) →
    (∀ t, (t, t) ∈ K → S.r t t = L ∧ S.A t t = 0 ∧
      |S.Q t t - qStar| ≤ Bboundary * eta) →
    ∀ p ∈ K, |S.Q p.1 p.2 - qStar| ≤ Cq * eta ∧ |S.Q p.1 p.2| ≤ 2 ∧
      ‖F p.1 p.2‖ ≤ Cn * (Nphi + Nm) / S.r p.1 p.2 ^ 3 +
        Ce * (eta / S.r p.1 p.2 ^ 4 + eta / (L * S.r p.1 p.2)) := by
  obtain ⟨Cp, hCp, hchargePotential⟩ := Observation.outer_charge_potential_of_normalization Kstatic
      hK
  obtain ⟨Cn, hCn, hsourceConstants⟩ :=
    co_source_envelope_of_normalization (Kstatic + 1) Cp (by linarith only [hK]) hCp.le
  refine ⟨Cp, Cn, hCp, hCn, fun Bboundary hB => ?_⟩
  obtain ⟨Cq, hCq, hcharge⟩ := hchargePotential Bboundary hB
  obtain ⟨Ce, hCe, hsource⟩ := hsourceConstants Cq hCq.le
  refine ⟨Cq, Ce, hCq, hCe, ?_⟩
  intro S D e eta a b rho L qStar Nphi Nm H phiStar yStar mStar
  dsimp only
  intro hrho hrhoL heta hq hscale hsmall hNp hstop hNm hw hm hstatic hsub
    hcR hcl hcn hcm hcQ hcA hcp hct hbox hd hb
  let K := sidewaysTruncation S D a b rho L
  have hstopNorm : comparisonNorm K (scalarComparison S H phiStar) ≤ 1 := by
    apply (comparisonNorm_le_of_bound hNp hw).trans
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hstop
  have hpotential := hcharge S D e eta a b rho L qStar H phiStar
    (zero_lt_one.trans_le hrho) (hrho.trans hrhoL) hq hscale hsmall hstopNorm
    (fun p hp => (hstatic p hp).1) hsub hcR hcl hcn hcm hcQ hcA hcp hct
    (fun p hp => ⟨(hbox p hp).1,
      abs_le.mpr ⟨(hbox p hp).2.2.1.1, (hbox p hp).2.2.1.2.trans (by norm_num)⟩,
      (hbox p hp).2.2.2⟩) hd hb
  intro p hp
  have hr : 1 ≤ S.r p.1 p.2 := hrho.trans hp.2.1
  have hrp : 0 < S.r p.1 p.2 := zero_lt_one.trans_le hr
  have hstat := hstatic p hp
  have hpsi : ‖shiftedRphi S H p.1 p.2‖ ≤ Kstatic + 1 := by
    calc
      _ = ‖scalarComparison S H phiStar p.1 p.2 +
          (S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := by
        simp only [scalarComparison, sub_add_cancel]
      _ ≤ ‖scalarComparison S H phiStar p.1 p.2‖ +
          ‖(S.r p.1 p.2 : ℂ) * phiStar (S.r p.1 p.2)‖ := norm_add_le _ _
      _ ≤ Kstatic + 1 := by linarith only [hw p hp, hstat.1, hstop]
  have hn : 0 ≤ -S.nu p.1 p.2 := neg_nonneg.mpr (hbox p hp).2.2.1.2
  have hn1 : -S.nu p.1 p.2 ≤ 1 := by linarith only [(hbox p hp).2.2.1.1]
  have hl1 : S.lam p.1 p.2 ≤ 1 := by linarith only [(hbox p hp).2.1]
  have hprod : (-S.nu p.1 p.2) * S.lam p.1 p.2 ∈ Icc 0 1 :=
    ⟨mul_nonneg hn (hbox p hp).1.le,
      (mul_le_mul hn1 hl1 (hbox p hp).1.le zero_le_one).trans_eq (by norm_num)⟩
  have hpoint := hsource (S.r p.1 p.2) L (S.m p.1 p.2) (mStar (S.r p.1 p.2))
    (S.Q p.1 p.2) qStar e eta (S.A p.1 p.2)
    ((-S.nu p.1 p.2) * S.lam p.1 p.2) (S.lam p.1 p.2) Nphi Nm
    H (shiftedRphi S H p.1 p.2) (scalarComparison S H phiStar p.1 p.2)
    (yStar (S.r p.1 p.2)) (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2))
    hr (hrp.trans_le hp.2.2) heta
    (by rw [abs_of_nonneg (hbox p hp).2.2.2.1.1]; exact (hbox p hp).2.2.2.1.2)
    (hbox p hp).2.2.2.2 hstat.2.2.2 hprod ⟨(hbox p hp).1.le, hl1⟩
    (hpotential p hp).2.1 hq (hpotential p hp).1 hscale (hpotential p hp).2.2.2
    (hw p hp) (by simpa only [massComparison, Real.norm_eq_abs] using hm p hp)
    hpsi (hstat.2.1.trans (by gcongr; linarith only [hK]))
    (hstat.2.2.1.trans (by gcongr; linarith only [hK]))
  refine ⟨(hpotential p hp).1, (hpotential p hp).2.1, ?_⟩
  convert hpoint using 1
  simp only [Fields.mu]
  congr 1
  push_cast
  ring

private theorem outer_absorb_normalized {k q D F N : ℝ}
    (hk : 0 ≤ k) (hk' : k ≤ 1 / 64) (hq : 0 < q) (hq' : q ≤ 1)
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hF' : F ≤ 1) (hN : 0 ≤ N) (hN' : N ≤ 4)
    (hs : F ≤ D + k * (F + N))
    (hm : N ≤ D * q + k * (F + F ^ 2) + k * q * N + k * q ^ 2 * N ^ 2) :
    F ≤ 4 * D ∧ N ≤ (2 + 16 * (k / q)) * D * q := by
  have hFsq : F ^ 2 ≤ F := by nlinarith only [hF, hF']
  have hNsq : N ^ 2 ≤ 4 * N := by nlinarith only [hN, hN']
  have hqSq : q ^ 2 ≤ 1 := by nlinarith only [hq.le, hq']
  have hkq : k * q ≤ k := mul_le_of_le_one_right hk hq'
  have hkqSq : k * q ^ 2 ≤ k := mul_le_of_le_one_right hk hqSq
  have hmass : N ≤ D * q + 2 * k * F + 5 * k * N := by
    have h1 := mul_le_mul_of_nonneg_left hFsq hk
    have h2 := mul_le_mul_of_nonneg_left hNsq (mul_nonneg hk (sq_nonneg q))
    have h3 := mul_le_mul_of_nonneg_right hkq hN
    have h4 := mul_le_mul_of_nonneg_right hkqSq (by linarith only [hN] : 0 ≤ 4 * N)
    nlinarith only [hm, h1, h2, h3, h4]
  have hmass' : N ≤ 2 * D * q + 4 * k * F := by
    have h5 := mul_le_mul_of_nonneg_right hk' hN
    nlinarith only [hmass, h5, hN]
  have hkSq : k ^ 2 ≤ k / 64 := by nlinarith only [hk, hk']
  have hscalar : F ≤ 4 * D := by
    have h1 := mul_le_mul_of_nonneg_left hmass' hk
    have h2 := mul_le_mul_of_nonneg_left hkq hD
    have h3 := mul_le_mul_of_nonneg_right hk' hD
    have h4 := mul_le_mul_of_nonneg_right hk' hF
    have h5 := mul_le_mul_of_nonneg_right hkSq hF
    nlinarith only [hs, h1, h2, h3, h4, h5, hD]
  refine ⟨hscalar, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hscalar hk
  have heq : (2 + 16 * (k / q)) * D * q = 2 * D * q + 16 * k * D := by
    field_simp [hq.ne']
  rw [heq]
  nlinarith only [hmass', h1]

/-- [internal]
Universal neutral absorption. The cutoff `64*(c+1)` is chosen after the
nonnegative universal coefficient `c`, before every error, radius and
solution datum. The mass coefficient depends only on `c`. -/
theorem co_outer_close (c : ℝ) (hc : 0 ≤ c) :
    ∃ Lmin : ℝ, 0 < Lmin ∧ ∀ (D L₀ F N : ℝ),
      Lmin ≤ L₀ → 0 ≤ D → 0 ≤ F → F ≤ 1 → 0 ≤ N → N ≤ 4 →
      F ≤ D + (c / L₀) * (F + N) →
      N ≤ D / L₀ + (c / L₀) * (F + F ^ 2) +
        (c / L₀ ^ 2) * N + (c / L₀ ^ 3) * N ^ 2 →
      F ≤ 4 * D ∧ N ≤ (2 + 16 * c) * D / L₀ := by
  refine ⟨64 * (c + 1), by positivity, ?_⟩
  intro D L₀ F N hL hD hF hF' hN hN' hs hm
  have hLpos : 0 < L₀ := lt_of_lt_of_le (by positivity) hL
  have hLone : 1 ≤ L₀ := by linarith only [hc, hL]
  have hk : c / L₀ ≤ 1 / 64 := (div_le_iff₀ hLpos).mpr (by linarith only [hL])
  have hq : 1 / L₀ ≤ 1 := (div_le_one hLpos).mpr hLone
  have hm' : N ≤ D * (1 / L₀) + (c / L₀) * (F + F ^ 2) +
      (c / L₀) * (1 / L₀) * N + (c / L₀) * (1 / L₀) ^ 2 * N ^ 2 := by
    convert hm using 1
    ring
  have hh := outer_absorb_normalized (div_nonneg hc hLpos.le) hk
    (by positivity : 0 < 1 / L₀) hq hD hF hF' hN hN' hs hm'
  refine ⟨hh.1, ?_⟩
  convert hh.2 using 1
  field_simp

namespace Observation

/-- [internal]
The continuous scalar maximum cannot cross `1` when every point satisfying
that temporary bound improves to `1/2`. The argument includes depth zero
and a degenerate depth interval. -/
theorem outer_stop_removed {F : ℝ → ℝ} {dmax : ℝ}
    (hF : ContinuousOn F (Icc 0 dmax)) (hzero : F 0 ≤ 1 / 2)
    (himprove : ∀ d ∈ Icc 0 dmax, F d ≤ 1 → F d ≤ 1 / 2) :
    ∀ d ∈ Icc 0 dmax, F d ≤ 1 / 2 := by
  intro d hd
  by_cases h : F d ≤ 1
  · exact himprove d hd h
  · have hd' : 0 ≤ d := hd.1
    have hcont := hF.mono (Icc_subset_Icc le_rfl hd.2)
    obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc hd' hcont
      (show (1 : ℝ) ∈ Icc (F 0) (F d) from ⟨by linarith only [hzero], le_of_not_ge h⟩)
    have hh := himprove x ⟨hx.1, hx.2.trans hd.2⟩ (by rw [hFx])
    rw [hFx] at hh
    norm_num at hh

/-- [internal]
Continuous-depth closure from the prior scalar and mass estimates. The
cutoff depends only on the universal neutral coefficient `c`, and is
chosen before every error, radius, depth interval and maximum profile.
The actual profiles are supplied by `continuousOn_outer_radius_maximum`;
every consumer must prove the two polynomial estimates on its own cuts. -/
theorem outer_depth_continuation_of_estimates (c : ℝ) (hc : 0 ≤ c) :
    ∃ Lmin : ℝ, 0 < Lmin ∧ ∀ (D L₀ dmax : ℝ) (F N : ℝ → ℝ),
      Lmin ≤ L₀ → 0 ≤ D → 4 * D ≤ 1 / 2 →
      ContinuousOn F (Icc 0 dmax) → F 0 ≤ 1 / 2 →
      (∀ d ∈ Icc 0 dmax, 0 ≤ F d ∧ 0 ≤ N d ∧ N d ≤ 4) →
      (∀ d ∈ Icc 0 dmax, F d ≤ 1 →
        F d ≤ D + (c / L₀) * (F d + N d) ∧
        N d ≤ D / L₀ + (c / L₀) * (F d + (F d) ^ 2) +
          (c / L₀ ^ 2) * N d + (c / L₀ ^ 3) * (N d) ^ 2) →
      ∀ d ∈ Icc 0 dmax, F d ≤ 4 * D ∧ N d ≤ (2 + 16 * c) * D / L₀ := by
  obtain ⟨Lmin, hLmin, habs⟩ := co_outer_close c hc
  refine ⟨Lmin, hLmin, ?_⟩
  intro D L₀ dmax F N hL hD hsmall hcont hzero hbox hest
  have hclose (d : ℝ) (hd : d ∈ Icc 0 dmax) (hF : F d ≤ 1) :
      F d ≤ 4 * D ∧ N d ≤ (2 + 16 * c) * D / L₀ :=
    habs D L₀ (F d) (N d) hL hD (hbox d hd).1 hF
      (hbox d hd).2.1 (hbox d hd).2.2 (hest d hd hF).1 (hest d hd hF).2
  have hstop := outer_stop_removed hcont hzero
    (fun d hd hF => (hclose d hd hF).1.trans hsmall)
  exact fun d hd => hclose d hd ((hstop d hd).trans (by norm_num))

end Observation

end EmcsfAcExtension.Global
