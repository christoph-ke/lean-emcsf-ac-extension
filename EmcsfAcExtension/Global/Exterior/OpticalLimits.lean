module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Global.Exterior.OpticsPast
import EmcsfAcExtension.Global.Exterior.OpticalTails

/-! # Uniform optical limits from split incoming tails

The incoming integrals are split at one fixed proper row. Continuity
on that row controls all labels between the current row and zero;
the common incoming tail then tends to zero.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The split-row argument of `charged_SF_new_version.tex:L1205–L1211`, given its incoming
logarithmic increment estimate. The consumer derives that estimate from
the radius equation and the integrable adaptive weight. The tail and
cutoffs may depend on the fixed original development. -/
theorem uniform_log_lam_difference_of_tail {ui e ub : ℝ} {S : Fields}
    (h : OriginalData ui e S) (ell tail : ℝ → ℝ) (hub : ub ∈ Ioo ui 0)
    (htail : Tendsto tail (𝓝[<] 0) (𝓝 0))
    (hincrement : ∀ s ∈ Ico ub 0, ∀ p ∈ adaptiveExterior S ui s ell,
      |Real.log (S.lam p.1 p.2) - Real.log (S.lam p.1 0)| ≤
        |Real.log (S.lam s p.2) - Real.log (S.lam s 0)| + 2 * tail s) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ub 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell,
        |Real.log (S.lam p.1 p.2) - Real.log (S.lam p.1 0)| < ε := by
  intro ε hε
  have he : ∀ᶠ s in 𝓝[<] (0 : ℝ), s ∈ Ioo ub 0 ∧ tail s < ε / 8 := by
    filter_upwards [Ioo_mem_nhdsLT hub.2,
      htail.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 8))] with s hs hb
    exact ⟨hs, hb⟩
  obtain ⟨s, hs, hTs⟩ := he.exists
  have hsrow : outSeg s s 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hs.2.le).2 ⟨hub.1.le.trans hs.1.le, hs.2, le_rfl, le_rfl⟩
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hsrow
  have clog := cl.log (fun v hv => (h.solution.lam_pos (s, v) (hsrow ⟨rfl, hv⟩)).ne')
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousWithinAt_iff.mp
    (clog 0 ⟨hs.2.le, le_rfl⟩) (ε / 2) (half_pos hε)
  let u₀ := max s (-δ / 2)
  have hu₀ : u₀ ∈ Ioo ub 0 :=
    ⟨lt_max_of_lt_left hs.1, max_lt hs.2 (by linarith)⟩
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hv : p.2 ∈ Icc s 0 :=
    ⟨(le_max_left s (-δ / 2)).trans (hp.2.1.trans hp.1.2.2.1), hp.1.2.2.2⟩
  have hvδ : dist p.2 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hp.1.2.2.2]
    have hb := (le_max_right s (-δ / 2)).trans (hp.2.1.trans hp.1.2.2.1)
    linarith
  have hbase := hδb hv hvδ
  rw [Real.dist_eq] at hbase
  have hinc := hincrement s ⟨hs.1.le, hs.2⟩ p
    ⟨hp.1, (le_max_left s (-δ / 2)).trans hp.2.1, hp.2.2⟩
  linarith only [hbase, hinc, hTs, hε]

/-- [internal]
Uniform convergence of logarithmic row differences and the positive
terminal lambda limit imply uniform convergence of lambda. The limiting
value is the explicit terminal witness; no selected constant is defined. -/
theorem uniform_lam_of_log_difference {ui e ub lam₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (ell : ℝ → ℝ) (hub : ub ∈ Ioo ui 0) (hlam₀ : 0 < lam₀)
    (hterminal : Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀))
    (hdifference : ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ub 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell,
        |Real.log (S.lam p.1 p.2) - Real.log (S.lam p.1 0)| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ub 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell, |S.lam p.1 p.2 - lam₀| < ε := by
  have hlogt := (Real.continuousAt_log hlam₀.ne').tendsto.comp hterminal
  intro ε hε
  have hcont : ContinuousAt Real.exp (Real.log lam₀) := Real.continuous_exp.continuousAt
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨ud, hud, hdiff⟩ := hdifference (η / 2) (half_pos hη)
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo ub 0 ∧
      |Real.log (S.lam u 0) - Real.log lam₀| < η / 2 := by
    filter_upwards [Ioo_mem_nhdsLT hub.2,
      (Metric.tendsto_nhds.mp hlogt) (η / 2) (half_pos hη)] with u hu hb
    exact ⟨hu, by simpa only [Real.dist_eq, Function.comp_apply] using hb⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let ut := max d ub / 2
  have hut : ut ∈ Ioo ub 0 := by
    have hm0 := max_lt hd hub.2
    dsimp [ut]
    constructor <;> linarith [le_max_right d ub]
  refine ⟨max ud ut, ⟨lt_max_of_lt_left hud.1, max_lt hud.2 hut.2⟩, ?_⟩
  intro p hp
  have hup : p.1 ∈ Ioo d 0 := by
    refine ⟨?_, hp.1.2.1⟩
    have hb := (le_max_right ud ut).trans hp.2.1
    dsimp [ut] at hb
    have hm0 := max_lt hd hub.2
    linarith [le_max_left d ub]
  have hterm := (hdb hup).2
  have hrow := hdiff p ⟨hp.1, (le_max_left ud ut).trans hp.2.1, hp.2.2⟩
  have hlog : |Real.log (S.lam p.1 p.2) - Real.log lam₀| < η := by
    have hb := abs_sub_le (Real.log (S.lam p.1 p.2))
      (Real.log (S.lam p.1 0)) (Real.log lam₀)
    linarith only [hb, hrow, hterm]
  have hdlog : dist (Real.log (S.lam p.1 p.2)) (Real.log lam₀) < η := by
    simpa only [Real.dist_eq] using hlog
  simpa only [Real.exp_log (h.solution.lam_pos p hp.1), Real.exp_log hlam₀,
    Real.dist_eq] using hηb hdlog

/-- [internal]
Conditional terminal consumer for `c:exterior#uniform-optical-limits`.
The radius collapse, radial mass characterization, terminal scalar bound
and positive terminal lambda limit are explicit terminal inputs. All
coefficient, invariance and split-tail hypotheses are discharged here.
The limiting lambda and the cutoffs may depend on the original solution;
the numerical optical coefficients are uniform in all data. -/
theorem uniform_optical_limits_of_terminal {ui e C k lam₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hlam₀ : 0 < lam₀)
    (hterminal : Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀)) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      |S.lam p.1 p.2 - lam₀| < ε ∧ |S.nu p.1 p.2 / S.nu p.1 0 - 1| < ε := by
  obtain ⟨uc, huc, hcoeff⟩ := incoming_optical_majorant_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨up, hup, hpast⟩ := incoming_past_invariance_of_terminal h M ell hR hC hk hLip
    hcollapse hmass hell hellsmall hsmall hphi
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ), u ∈ Ioo ui 0 ∧ S.r u 0 < R₀ := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hcollapse.eventually (Iio_mem_nhds hR)]
      with u hu hr
    exact ⟨hu, hr⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let ur := max d ui / 2
  have hur : ur ∈ Ioo ui 0 := by
    have hm0 := max_lt hd h.ui_neg
    dsimp [ur]
    constructor <;> linarith [le_max_right d ui]
  let ub := max uc (max up ur)
  have hub : ub ∈ Ioo ui 0 :=
    ⟨lt_max_of_lt_left huc.1, max_lt huc.2 (max_lt hup.2 hur.2)⟩
  have hcoef (p : ℝ × ℝ) (hp : p ∈ adaptiveExterior S ui ub ell) :
      0 < ell (terminalRadius S p.1) ∧
      |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤
        264 * (-S.nu p.1 0) * terminalMass S p.1 / ell (terminalRadius S p.1) ^ 2 :=
    hcoeff p ⟨hp.1, (le_max_left uc (max up ur)).trans hp.2.1, hp.2.2⟩
  have hinv (p : ℝ × ℝ) (hp : p ∈ adaptiveExterior S ui ub ell)
      (s : ℝ) (hs : s ∈ Icc ub p.1) : (s, p.2) ∈ adaptiveExterior S ui ub ell := by
    have hbup : up ≤ ub := (le_max_left up ur).trans (le_max_right uc (max up ur))
    have hp' : p ∈ adaptiveExterior S ui up ell := ⟨hp.1, hbup.trans hp.2.1, hp.2.2⟩
    have hs' := (hpast p hp').1 s ⟨hbup.trans hs.1, hs.2⟩
    exact ⟨hs'.1, hs.1, hs'.2.2⟩
  have hRange (s : ℝ) (hs : s ∈ Ico ub 0) : S.r s 0 ≤ R₀ := by
    have hs' : s ∈ Ioo d 0 := by
      refine ⟨?_, hs.2⟩
      have hb : ur ≤ s := (le_max_right up ur).trans
        ((le_max_right uc (max up ur)).trans hs.1)
      dsimp [ur] at hb
      have hm0 := max_lt hd h.ui_neg
      linarith [le_max_left d ui]
    exact (hdb hs').2.le
  let tail := fun s => 264 *
    (∫⁻ R in Ioc 0 (S.r s 0), ENNReal.ofReal (M R / ell R ^ 2)).toReal
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have htail : Tendsto tail (𝓝[<] 0) (𝓝 0) := (optical_tail_tendsto_zero hR hint).comp hRt
  have hincrement (s : ℝ) (hs : s ∈ Ico ub 0) (p : ℝ × ℝ)
      (hp : p ∈ adaptiveExterior S ui s ell) :
      |Real.log (S.lam p.1 p.2) - Real.log (S.lam p.1 0)| ≤
        |Real.log (S.lam s p.2) - Real.log (S.lam s 0)| + 2 * tail s := by
    have hp' : p ∈ adaptiveExterior S ui ub ell := ⟨hp.1, hs.1.trans hp.2.1, hp.2.2⟩
    have hℓ := (hcoef p hp').1
    have hr : 0 < S.r p.1 p.2 := hℓ.trans_le hp.2.2
    have huv : p.1 < p.2 := by
      rcases hp.1.2.2.1.eq_or_lt with heq | hlt
      · have hpaxis : (p.1, p.1) ∈ origDomain ui :=
          ⟨hp.1.1, hp.1.2.1, le_rfl, hp.1.2.1.le⟩
        rw [← heq, (h.solution.axis p.1 hpaxis).1] at hr
        exact False.elim (lt_irrefl _ hr)
      · exact hlt
    have hp0 : (p.1, 0) ∈ adaptiveExterior S ui ub ell :=
      ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩, hp'.2.1,
        hp.2.2.trans (radius_le_terminal h hp.1)⟩
    have hv := incoming_log_lam_tail_le_of_majorant h M ell hp.2.1 huv (hRange s hs)
      hmass hint (fun u hu => hinv p hp' u ⟨hs.1.trans hu.1, hu.2⟩)
      (fun q hq => (hcoef q hq).2)
    have h0 := incoming_log_lam_tail_le_of_majorant h M ell hp.2.1 hp.1.2.1 (hRange s hs)
      hmass hint (fun u hu => hinv (p.1, 0) hp0 u ⟨hs.1.trans hu.1, hu.2⟩)
      (fun q hq => (hcoef q hq).2)
    have h₁ := abs_sub_le (Real.log (S.lam p.1 p.2)) (Real.log (S.lam s p.2))
      (Real.log (S.lam p.1 0))
    have h₂ := abs_sub_le (Real.log (S.lam s p.2)) (Real.log (S.lam s 0))
      (Real.log (S.lam p.1 0))
    rw [abs_sub_comm (Real.log (S.lam p.1 0))] at h0
    change _ ≤ tail s at hv h0
    linarith only [h₁, h₂, hv, h0]
  have hlambda := uniform_lam_of_log_difference h ell hub hlam₀ hterminal
    (uniform_log_lam_difference_of_tail h ell tail hub htail hincrement)
  intro ε hε
  obtain ⟨ul, hul, hl⟩ := hlambda ε hε
  obtain ⟨un, hun, hn⟩ := uniform_nu_ratio_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi ε hε
  refine ⟨max ul un, ⟨lt_max_of_lt_left (hub.1.trans hul.1), max_lt hul.2 hun.2⟩, ?_⟩
  intro p hp
  exact ⟨hl p ⟨hp.1, (le_max_left ul un).trans hp.2.1, hp.2.2⟩,
    hn p ⟨hp.1, (le_max_right ul un).trans hp.2.1, hp.2.2⟩⟩

/-- [internal]
Conditional terminal consumer for `c:exterior#exterior-lambda-lower-bound`.
The witness `lam₀/2` depends only on the explicit positive terminal limit.
The uniform optical limit is proved first from split logarithmic tails;
this reverses the paper's order of these two consequences without adding
an assumption or changing either conclusion. -/
theorem exterior_lambda_lower_bound_of_terminal {ui e C k lam₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hk : 0 < k ∧ k < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k) ell (Ioc 0 R₀))
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))))
    (hlam₀ : 0 < lam₀)
    (hterminal : Tendsto (fun u => S.lam u 0) (𝓝[<] 0) (𝓝 lam₀)) :
    ∃ c > 0, ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell, c ≤ S.lam p.1 p.2 := by
  obtain ⟨u₀, hu₀, hb⟩ := uniform_optical_limits_of_terminal h M ell hR hC hk hLip
    hcollapse hmass hell hellsmall hsmall hint hphi hlam₀ hterminal (lam₀ / 2) (half_pos hlam₀)
  refine ⟨lam₀ / 2, half_pos hlam₀, u₀, hu₀, ?_⟩
  intro p hp
  have hl := (abs_lt.mp (hb p hp).1).1
  linarith

end EmcsfAcExtension.Global.Exterior
