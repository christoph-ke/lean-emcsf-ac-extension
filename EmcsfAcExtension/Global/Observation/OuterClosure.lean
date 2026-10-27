module

public import EmcsfAcExtension.Global.Observation.Domains
public import EmcsfAcExtension.Global.Observation.OuterMass

/-! # Absorption and radial-depth continuation for the outer comparison

The outer cylinder is the normalized diagonal. All suprema below refer to
the actual compact sideways truncations, without a normalized-chart
`IsSolution` assertion. Source: `charged_SF_new_version.tex:L2518–L2544`, approved
internal project record, `eq:co-outer-close` and the outer-domain continuation argument.
-/

public section

open Set Filter Topology MeasureTheory Complex

namespace EmcsfAcExtension.Global

namespace Observation

/-- [internal]
The actual scalar and mass comparison norms obey the closed outer bounds
on the entire given truncation. The universal cutoff is chosen after `c`
alone. The error and boundary bound are subsequently small. The two prior
polynomial estimates remain explicit inputs to this internal helper;
its consumer derives them on these same literal truncations. -/
theorem outer_domain_continuation_of_estimates (c : ℝ) (hc : 0 ≤ c) :
    ∃ Lmin : ℝ, 0 < Lmin ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ) (phiStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b error L₀ L : ℝ),
    let K := sidewaysTruncation S D a b L₀ L
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖scalarComparison S H phiStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (L - d) L)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (L - d) L)
    Lmin ≤ L₀ → L₀ ≤ L → 0 ≤ error → 4 * error ≤ 1 / 2 → IsCompact K →
    ContinuousOn (Function.uncurry S.r) K →
    ContinuousOn (Function.uncurry (scalarComparison S H phiStar)) K →
    ContinuousOn (Function.uncurry (massComparison S mStar)) K →
    (∃ p ∈ K, S.r p.1 p.2 = L) →
    (∀ p ∈ K, sidewaysTriangle p.2 p.1 ⊆ K) →
    (∀ p ∈ K, S.r p.2 p.2 = L) →
    (∀ p ∈ K, HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1) →
    (∀ p ∈ K, S.nu p.1 p.2 < 0) →
    (∀ p ∈ K, ‖massComparison S mStar p.1 p.2‖ ≤ 4) →
    comparisonNorm (sidewaysTruncation S D a b L L) (scalarComparison S H phiStar) ≤
      ENNReal.ofReal (1 / 2) →
    (∀ d ∈ Icc 0 (L - L₀), F d ≤ 1 →
      F d ≤ error + (c / L₀) * (F d + N d) ∧
      N d ≤ error / L₀ + (c / L₀) * (F d + (F d) ^ 2) +
        (c / L₀ ^ 2) * N d + (c / L₀ ^ 3) * (N d) ^ 2) →
    comparisonNorm K (scalarComparison S H phiStar) ≤ ENNReal.ofReal (4 * error) ∧
      comparisonNorm K (massComparison S mStar) ≤ ENNReal.ofReal ((2 + 16 * c) * error / L₀) := by
  obtain ⟨Lmin, hLmin, hclosure⟩ := outer_depth_continuation_of_estimates c hc
  refine ⟨Lmin, hLmin, ?_⟩
  intro S D H phiStar mStar a b error L₀ L
  dsimp only
  intro hL hLL herror hsmall hK hr hf hg hbase htriangle hdiag hderiv hnu hmass hzero hest
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖scalarComparison S H phiStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (L - d) L)
  let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b (L - d) L)
  have hfmax := continuousOn_outer_radius_maximum hK hr hf hbase htriangle hdiag hderiv hnu
  have hgmax := continuousOn_outer_radius_maximum hK hr hg hbase htriangle hdiag hderiv hnu
  have h0 : (0 : ℝ) ∈ Icc 0 (L - L₀) := ⟨le_rfl, sub_nonneg.mpr hLL⟩
  have hF0 : F 0 ≤ 1 / 2 := by
    have heq := hfmax.2.2 0 h0
    simp only [sub_zero] at heq
    rw [heq] at hzero
    simpa only [F, sub_zero] using
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hzero
  have hbox (d : ℝ) (hd : d ∈ Icc 0 (L - L₀)) : 0 ≤ F d ∧ 0 ≤ N d ∧ N d ≤ 4 := by
    refine ⟨Real.sSup_nonneg ?_, Real.sSup_nonneg ?_, Real.sSup_le ?_ (by norm_num)⟩
    · rintro _ ⟨p, hp, rfl⟩; exact norm_nonneg _
    · rintro _ ⟨p, hp, rfl⟩; exact norm_nonneg _
    · rintro _ ⟨p, hp, rfl⟩
      exact hmass p ((sidewaysTruncation_depth_eq S D a b L₀ L hd ▸ hp).1)
  have hclose := hclosure error L₀ (L - L₀) F N hL herror hsmall hfmax.1 hF0 hbox hest
  have hend : L - L₀ ∈ Icc 0 (L - L₀) := ⟨sub_nonneg.mpr hLL, le_rfl⟩
  have hfinal := hclose (L - L₀) hend
  simp only [F, N, sub_sub_cancel] at hfinal
  have hfeq := hfmax.2.2 (L - L₀) hend
  have hgeq := hgmax.2.2 (L - L₀) hend
  simp only [sub_sub_cancel] at hfeq hgeq
  rw [hfeq, hgeq]
  exact ⟨ENNReal.ofReal_le_ofReal hfinal.1, ENNReal.ofReal_le_ofReal hfinal.2⟩


/-- [internal]
Outer comparison from the exact incoming transport, the prior pointwise source
and charge bounds on each stopped truncation, and normalized outgoing component
equations. Both regional polynomial estimates are derived here. The universal
cutoff and final mass coefficient depend only on `Kstatic,Cn`; boundary/electric
constants are chosen next, before every radius, field and error. All suprema
and every radial trace belong to the same literal sideways truncation. -/
theorem outer_comparison_of_source_envelope (Kstatic Cn : ℝ)
    (hKs : 0 ≤ Kstatic) (hCn : 0 ≤ Cn) :
    ∃ Lmin Cm : ℝ, 0 < Lmin ∧ 0 < Cm ∧ ∀ Ct Ce B : ℝ,
    0 ≤ Ct → 0 ≤ Ce → 0 ≤ B → ∃ Cboundary Celectric : ℝ,
    0 < Cboundary ∧ 0 < Celectric ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H : ℂ) (phiStar yStar : ℝ → ℂ)
      (mStar kStar : ℝ → ℝ) (a b L₀ L epsilon eta qStar e : ℝ)
      (wV source : ℝ → ℝ → ℂ) (connection : ℝ → ℝ → ℝ),
    let R := sidewaysTruncation S D a b L₀ L
    Lmin ≤ L₀ → L₀ ≤ L → 0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ eta → eta ≤ 1 →
    4 * (Cboundary * epsilon + Celectric * eta) ≤ 1 / 2 → |qStar| ≤ 1 →
    IsCompact R → ContinuousOn (Function.uncurry S.r) R →
    ContinuousOn (Function.uncurry S.nu) R → ContinuousOn (Function.uncurry S.lam) R →
    ContinuousOn (Function.uncurry S.A) R → ContinuousOn (Function.uncurry S.phi) R →
    ContinuousOn (Function.uncurry S.theta) R → ContinuousOn (Function.uncurry S.m) R →
    ContinuousOn (Function.uncurry S.Q) R → AbsolutelyContinuousOnInterval mStar L₀ L →
    ContinuousOn phiStar (Icc L₀ L) → ContinuousOn yStar (Icc L₀ L) →
    ContinuousOn kStar (Icc L₀ L) →
    (∀ s ∈ Icc L₀ L, HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r)
      (phiStar s + yStar s) s) →
    (∀ s ∈ Icc L₀ L, HasDerivAt (fun r => phiStar r + yStar r)
      ((-kStar s / s : ℝ) * yStar s) s) →
    (∀ s ∈ Ioo L₀ L, HasDerivAt mStar
      ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s) →
    (∀ s ∈ Icc L₀ L, |mStar s| ≤ 2 ∧ ‖yStar s‖ ≤ Kstatic / s ∧
      |1 - 2 * mStar s / s| ≤ 2) →
    (∃ p ∈ R, S.r p.1 p.2 = L) →
    (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) →
    (∀ p ∈ R, HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1) →
    (∀ p ∈ R, HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2) →
    (∀ p ∈ R, HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2) →
    (∀ p ∈ R, HasDerivAt (fun u => S.lam u p.2) (S.rUV p.1 p.2) p.1) →
    (∀ p ∈ R, HasDerivAt (fun u => S.phi u p.2) (S.phiU e p.1 p.2) p.1) →
    (∀ p ∈ R, HasDerivAt (fun u => S.theta u p.2) (S.thetaU e p.1 p.2) p.1) →
    (∀ p ∈ R, HasDerivAt (S.phi p.1) (S.theta p.1 p.2 / (S.r p.1 p.2 : ℂ)) p.2) →
    wV = (fun u v => (S.lam u v : ℂ) *
      (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v) →
    connection = (fun u v => e * S.A u v) →
    source = (fun u v =>
      let k := (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v);
      -(((-S.nu u v) * S.lam u v * k / S.r u v ^ 2 : ℝ) : ℂ) * scalarComparison S H phiStar u v +
      (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) * yStar (S.r u v) *
        ((k - kStar (S.r u v) : ℝ) : ℂ) -
      I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) * (H + (phiStar (S.r u v) + yStar (S.r u v))) +
      I * ((e * (-S.nu u v) * S.lam u v * S.Q u v / ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
        (shiftedRphi S H u v + (S.r u v : ℂ) * H)) →
    (∀ p ∈ R, S.nu p.1 p.2 ≤ -(1 / 8) ∧ 1 / 8 ≤ S.lam p.1 p.2 ∧
      S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2) →
    (∀ t, (t, t) ∈ R → S.r t t = L ∧
      ‖scalarComparison S H phiStar t t‖ ≤ Ct * epsilon ∧
      ‖wV t t‖ ≤ epsilon / (2 * L) ∧ |massComparison S mStar t t| ≤ Ct * epsilon / L) →
    (∀ ρ ∈ Icc L₀ L, comparisonNorm (sidewaysTruncation S D a b ρ L)
      (scalarComparison S H phiStar) ≤ 1 → ∀ p ∈ sidewaysTruncation S D a b ρ L,
      |S.Q p.1 p.2| ≤ 2 ∧ |S.Q p.1 p.2 - qStar| ≤ B * eta) →
    (∀ ρ ∈ Icc L₀ L, ∀ Nphi Nm : ℝ, 0 ≤ Nphi → 0 ≤ Nm → Nphi ≤ 1 →
      comparisonNorm (sidewaysTruncation S D a b ρ L) (scalarComparison S H phiStar) ≤
        ENNReal.ofReal Nphi →
      comparisonNorm (sidewaysTruncation S D a b ρ L) (massComparison S mStar) ≤ ENNReal.ofReal Nm →
      ∀ p ∈ sidewaysTruncation S D a b ρ L,
      ‖source p.1 p.2‖ ≤ Cn * (Nphi + Nm) / (S.r p.1 p.2) ^ 3 +
        Ce * (eta / (S.r p.1 p.2) ^ 4 + eta / (L * S.r p.1 p.2))) →
    comparisonNorm R (scalarComparison S H phiStar) ≤
      ENNReal.ofReal (4 * (Cboundary * epsilon + Celectric * eta)) ∧
    comparisonNorm R (massComparison S mStar) ≤
      ENNReal.ofReal (Cm * (Cboundary * epsilon + Celectric * eta) / L₀) := by
  let CY := 64 * Cn + 1
  have hCY : 0 ≤ CY := by dsimp [CY]; positivity
  obtain ⟨CnM, hCnM, hmass⟩ := co_outer_mass_of_scalar_estimate Kstatic CY hKs hCY
  let c := CnM + 64 * Cn
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨Lbase, hLbase, hcontinuation⟩ := outer_domain_continuation_of_estimates c hc
  refine ⟨max Lbase 1, 2 + 16 * c, lt_of_lt_of_le hLbase (le_max_left _ _),
    by positivity, ?_⟩
  intro Ct Ce B hCt hCe hB
  obtain ⟨CbM, CeM, hCbM, hCeM, hmass⟩ := hmass (Ct + 4) (64 * Ce) B
    (by positivity) (by positivity) hB
  let CB := CbM + Ct + 4
  let CE := CeM + 96 * Ce
  refine ⟨CB, CE, by dsimp [CB]; positivity, by dsimp [CE]; positivity, ?_⟩
  intro S D H phiStar yStar mStar kStar a b L₀ L epsilon eta qStar e wV source connection
  dsimp only
  intro hL hLL he he1 heta heta1 hsmall hq hcompact hr hnuc hlamc hAc hphic htheta hm hQ hms
    hps hys hks hstaticRphi hstaticSecond hmsd hstatic hbase htriangle hrin hrout hmout
    hlamin hphiin hthetain hphiout hwVdef hconnection hsourceDef hbox hboundary hcharge hsource
  let R := sidewaysTruncation S D a b L₀ L
  let error := CB * epsilon + CE * eta
  have hL₀ : 1 ≤ L₀ := (le_max_right Lbase 1).trans hL
  have hL₀p : 0 < L₀ := zero_lt_one.trans_le hL₀
  have hLp : 0 < L := hL₀p.trans_le hLL
  have herror : 0 ≤ error := by dsimp [error, CB, CE]; positivity
  have hsectionIn {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :
      ContinuousOn (fun u => f u p.2) (Icc p.2 p.1) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => htriangle p hp (sidewaysTriangle_incoming hu))
  have hsectionOut {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
      (hc : ContinuousOn (Function.uncurry f) R) (p) (hp : p ∈ R) :
      ContinuousOn (f p.1) (Icc p.2 p.1) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => htriangle p hp (sidewaysTriangle_outgoing hv))
  have hpr := hps.comp hr (fun p hp => hp.2)
  have hyr := hys.comp hr (fun p hp => hp.2)
  have hrc : ContinuousOn (fun p : ℝ × ℝ => (S.r p.1 p.2 : ℂ)) R :=
    Complex.continuous_ofReal.comp_continuousOn hr
  have hf : ContinuousOn (Function.uncurry (scalarComparison S H phiStar)) R :=
    (hrc.mul (hphic.sub continuousOn_const)).sub (hrc.mul hpr)
  have hwVc : ContinuousOn (Function.uncurry wV) R := by
    rw [hwVdef]
    exact ((Complex.continuous_ofReal.comp_continuousOn hlamc).mul
      ((hphic.sub continuousOn_const).sub (hpr.add hyr))).add htheta
  have hopt (p) (hp : p ∈ R) : ContinuousOn (fun u => S.nu u p.2) (Icc p.2 p.1) ∧
      ContinuousOn (S.lam p.1) (Icc p.2 p.1) := ⟨hsectionIn hnuc p hp, hsectionOut hlamc p hp⟩
  have htransport (p) (hp : p ∈ R) :
      AbsolutelyContinuousOnInterval (fun u => wV u p.2) p.2 p.1 ∧
      IntervalIntegrable (fun u => connection u p.2) volume p.2 p.1 ∧
      IntervalIntegrable (fun u => source u p.2) volume p.2 p.1 ∧
      (∀ᵐ u ∂volume.restrict (Icc p.2 p.1),
        deriv (fun v => wV v p.2) u = -I * (connection u p.2 : ℂ) * wV u p.2 + source u p.2) := by
    have hpath (u) (hu : u ∈ Icc p.2 p.1) := htriangle p hp (sidewaysTriangle_incoming hu)
    have hrad : (fun u => S.r u p.2) '' Icc p.2 p.1 ⊆ Icc L₀ L := by
      rintro _ ⟨u, hu, rfl⟩; exact (hpath u hu).2
    have ht := co_wv_transport_of_normalization (e := e) H phiStar yStar kStar hp.1.2.2.1
      (hsectionIn hr p hp) (hsectionIn hnuc p hp) (hsectionIn hlamc p hp) (hsectionIn hm p hp)
      (hsectionIn hQ p hp) (hsectionIn hAc p hp) (hsectionIn hphic p hp) (hsectionIn htheta p hp)
      (fun u hu => (hL₀p.trans_le (hpath u hu).2.1).ne')
      (fun u hu => by linarith only [(hbox (u, p.2) (hpath u hu)).2.2.2])
      (hps.mono hrad) (hys.mono hrad) (hks.mono hrad)
      (fun u hu => hrin (u, p.2) (hpath u (Ioo_subset_Icc_self hu)))
      (fun u hu => hlamin (u, p.2) (hpath u (Ioo_subset_Icc_self hu)))
      (fun u hu => hphiin (u, p.2) (hpath u (Ioo_subset_Icc_self hu)))
      (fun u hu => hthetain (u, p.2) (hpath u (Ioo_subset_Icc_self hu)))
      (fun u hu => hstaticSecond (S.r u p.2) (hpath u (Ioo_subset_Icc_self hu)).2)
    simpa only [hwVdef, hconnection, hsourceDef] using ht.2.2.2
  have hac (p) (hp : p ∈ R) := (htransport p hp).1
  have hiB (p) (hp : p ∈ R) := (htransport p hp).2.1
  have hiF (p) (hp : p ∈ R) := (htransport p hp).2.2.1
  have heq (p) (hp : p ∈ R) := (htransport p hp).2.2.2
  have hw (p) (hp : p ∈ R) : HasDerivAt (scalarComparison S H phiStar p.1) (wV p.1 p.2) p.2 := by
    rw [hwVdef]
    exact scalar_comparison_out_deriv_of_normalization phiStar yStar
      (hL₀p.trans_le hp.2.1).ne' (hrout p hp) (hphiout p hp) (hstaticRphi (S.r p.1 p.2) hp.2)
  have hiV (p) (hp : p ∈ R) : IntervalIntegrable (wV p.1) volume p.2 p.1 :=
    (hsectionOut hwVc p hp).intervalIntegrable_of_Icc hp.1.2.2.1
  have hident (p) (_hp : p ∈ R) : (S.lam p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H -
      (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2))) + S.theta p.1 p.2 = wV p.1 p.2 := by
    rw [hwVdef]
  have hnu (p) (hp : p ∈ R) : S.nu p.1 p.2 < 0 := by linarith only [(hbox p hp).1]
  have hdiag (p) (hp : p ∈ R) : S.r p.2 p.2 = L :=
    (hboundary p.2 (htriangle p hp ⟨le_rfl, le_rfl, hp.1.2.2.1⟩)).1
  have hin := strictAntiOn_radius_incoming_of_normalization hr htriangle hrin hnu
  have hsub {ρ : ℝ} (hρ : L₀ ≤ ρ) : sidewaysTruncation S D a b ρ L ⊆ R :=
    sidewaysTruncation_mono_radius S D a b L hρ
  have htri {ρ : ℝ} (hρ : L₀ ≤ ρ) :=
    subtriangle_mem_larger_radius_of_normalization hr htriangle hrin hrout hnu
      (fun p hp => by linarith only [(hbox p hp).2.1]) ρ hρ
  have hmsc : ContinuousOn mStar (Icc L₀ L) := by
    simpa only [uIcc_of_le hLL] using hms.continuousOn
  have hg : ContinuousOn (Function.uncurry (massComparison S mStar)) R :=
    hm.sub (hmsc.comp hr (fun p hp => hp.2))
  have hmass4 (p) (hp : p ∈ R) : ‖massComparison S mStar p.1 p.2‖ ≤ 4 := by
    have hmb := (hbox p hp).2.2.1
    have hst := (hstatic (S.r p.1 p.2) hp.2).1
    change ‖S.m p.1 p.2 - mStar (S.r p.1 p.2)‖ ≤ 4
    apply (norm_sub_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg hmb.1, Real.norm_eq_abs]
    linarith only [hmb.2, hst]
  have hzero : comparisonNorm (sidewaysTruncation S D a b L L)
      (scalarComparison S H phiStar) ≤ ENNReal.ofReal (1 / 2) := by
    apply comparisonNorm_le_of_bound (by norm_num)
    intro p hp
    have hpR := hsub hLL hp
    have heqr : S.r p.1 p.2 = L := le_antisymm hp.2.2 hp.2.1
    have hd := (radius_eq_outer_iff_diagonal_of_normalization
      (fun p hp => hp.1.2.2.1) hdiag hin p hpR).mp heqr
    have hb := (hboundary p.2 (htriangle p hpR ⟨le_rfl, le_rfl, hpR.1.2.2.1⟩)).2.1
    have hbd : Ct * epsilon ≤ error := by
      dsimp [error, CB, CE]
      nlinarith only [mul_nonneg hCbM.le he, mul_nonneg hCeM.le heta,
        mul_nonneg hCe heta, he]
    rw [hd]
    exact hb.trans (hbd.trans (by linarith only [hsmall]))
  apply hcontinuation S D H phiStar mStar a b error L₀ L
    ((le_max_left Lbase 1).trans hL) hLL herror hsmall hcompact hr hf hg hbase
    htriangle hdiag hrin hnu hmass4 hzero
  intro d hd hstop
  let ρ := L - d
  have hρ : ρ ∈ Icc L₀ L := ⟨by dsimp [ρ]; linarith only [hd.2],
    by dsimp [ρ]; linarith only [hd.1]⟩
  let Nphi := sSup ((fun p : ℝ × ℝ => ‖scalarComparison S H phiStar p.1 p.2‖) ''
    sidewaysTruncation S D a b ρ L)
  let Nm := sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
    sidewaysTruncation S D a b ρ L)
  have hNp : 0 ≤ Nphi := Real.sSup_nonneg (by rintro _ ⟨p, hp, rfl⟩; exact norm_nonneg _)
  have hNm : 0 ≤ Nm := Real.sSup_nonneg (by rintro _ ⟨p, hp, rfl⟩; exact norm_nonneg _)
  have hfmax := continuousOn_outer_radius_maximum hcompact hr hf hbase htriangle hdiag hrin hnu
  have hgmax := continuousOn_outer_radius_maximum hcompact hr hg hbase htriangle hdiag hrin hnu
  have hFnorm : comparisonNorm (sidewaysTruncation S D a b ρ L)
      (scalarComparison S H phiStar) = ENNReal.ofReal Nphi := hfmax.2.2 d hd
  have hNnorm : comparisonNorm (sidewaysTruncation S D a b ρ L)
      (massComparison S mStar) = ENNReal.ofReal Nm := hgmax.2.2 d hd
  have hFpoint (p) (hp : p ∈ sidewaysTruncation S D a b ρ L) :
      ‖scalarComparison S H phiStar p.1 p.2‖ ≤ Nphi := by
    have hh := enorm_le_comparisonNorm (f := scalarComparison S H phiStar) hp
    rw [hFnorm, ← ofReal_norm] at hh
    exact (ENNReal.ofReal_le_ofReal_iff hNp).mp hh
  have hcharged := hcharge ρ hρ (by
    rw [hFnorm]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hstop)
  have hscalar := co_outer_sup_of_source_envelope Ct Cn Ce hCt hCn hCe wV source connection
    hL₀ hρ.1 hNp hNm he heta (htri hρ.1)
    (fun p hp => hrin p (hsub hρ.1 hp)) (fun p hp => hrout p (hsub hρ.1 hp))
    (fun p hp => hopt p (hsub hρ.1 hp))
    (fun p hp => ⟨(hbox p (hsub hρ.1 hp)).1, (hbox p (hsub hρ.1 hp)).2.1⟩)
    (fun t ht => ⟨(hboundary t (hsub hρ.1 ht)).1,
      (hboundary t (hsub hρ.1 ht)).2.1, (hboundary t (hsub hρ.1 ht)).2.2.1⟩)
    (fun p hp => hac p (hsub hρ.1 hp)) (fun p hp => hiB p (hsub hρ.1 hp))
    (fun p hp => hiF p (hsub hρ.1 hp)) (fun p hp => heq p (hsub hρ.1 hp))
    (fun p hp => hw p (hsub hρ.1 hp)) (fun p hp => hiV p (hsub hρ.1 hp))
    hFpoint (fun p hp => hident p (hsub hρ.1 hp))
    (hsource ρ hρ Nphi Nm hNp hNm hstop hFnorm.le hNnorm.le)
  have hpolyS : Nphi ≤ (Ct + 4) * epsilon + 64 * (Cn * (Nphi + Nm)) / L₀ + 96 * (Ce * eta) := by
    rw [hFnorm] at hscalar
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hscalar.2.1
  have hpolyM : Nm ≤ (CbM * epsilon + CeM * eta) / L₀ +
      (CnM / L₀) * (Nphi + Nphi ^ 2) + (CnM / L₀ ^ 2) * Nm + (CnM / L₀ ^ 3) * Nm ^ 2 := by
    apply Real.sSup_le _ (by positivity)
    rintro _ ⟨p, hp, rfl⟩
    have hpR := hsub hρ.1 hp
    have hpath := (sidewaysTruncation_paths (htri hρ.1 p hp)).2
    have hpathR (t) (ht : t ∈ Icc p.2 p.1) : (p.1, t) ∈ R := hsub hρ.1 (hpath t ht)
    have hcont {E : Type} [TopologicalSpace E] {f : ℝ → ℝ → E}
        (hc : ContinuousOn (Function.uncurry f) R) : ContinuousOn (f p.1) (Icc p.2 p.1) :=
      hc.comp (continuous_const.prodMk continuous_id).continuousOn hpathR
    obtain ⟨inv, hrL, hci, hmem, hrad, hleft, hright, hdi, hy, hmr, hQr, hmd, hmac, hradbox,
        henergy⟩ :=
      outgoing_radial_mass_data_of_normalization S hp.1.2.2.1
        (hL₀p.trans_le (hρ.1.trans hp.2.1)) (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
        (hcont hr) (hopt p hpR).2 (hcont htheta) (hcont hm) (hcont hQ)
        (fun t ht => hrout (p.1, t) (hpathR t (Ioo_subset_Icc_self ht)))
        (fun t ht => hmout (p.1, t) (hpathR t (Ioo_subset_Icc_self ht)))
        (fun t ht => ⟨by linarith only [(hbox (p.1, t) (hpathR t ht)).2.1],
          (hbox (p.1, t) (hpathR t ht)).2.2⟩)
    let y := fun s => S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)
    let mr := fun s => S.m p.1 (inv s)
    let Qr := fun s => S.Q p.1 (inv s)
    let dm := fun s => mr s - mStar s
    let gs := fun s => 1 - 2 * mStar s / s
    have hinterval : Icc (S.r p.1 p.2) L ⊆ Icc L₀ L := Icc_subset_Icc (hρ.1.trans hp.2.1) le_rfl
    have hmsr : AbsolutelyContinuousOnInterval mStar (S.r p.1 p.2) L := hms.mono (by
      rw [uIcc_of_le hrL, uIcc_of_le hLL]; exact hinterval)
    have hgs : ContinuousOn gs (Icc (S.r p.1 p.2) L) := continuousOn_const.sub
      ((continuousOn_const.mul (hmsc.mono hinterval)).div continuousOn_id
        (fun s hs => (hL₀p.trans_le (hinterval hs).1).ne'))
    have hD : AbsolutelyContinuousOnInterval dm (S.r p.1 p.2) L := hmac.sub hmsr
    have hbd : |dm L| ≤ (Ct + 4) * epsilon / L := by
      have hb := (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).2.2.2
      dsimp [dm, mr]
      rw [hright]
      have hRL := (hboundary p.1 (hpathR p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
      simpa only [massComparison, hRL] using hb.trans
        (div_le_div_of_nonneg_right (by nlinarith only [he] : Ct * epsilon ≤ (Ct + 4) * epsilon)
            hLp.le)
    have hY (s) (hs : s ∈ Icc (S.r p.1 p.2) L) :
        ‖y s - yStar s‖ ≤ (Ct + 4) * epsilon / L + CY * Nphi / s + CY * Nm / s ^ 2 +
          (64 * Ce) * eta / s ^ 3 + (64 * Ce) * eta / L * Real.log (L / s) := by
      have hh := hscalar.2.2 (p.1, inv s) (hpath (inv s) (hmem s))
      rw [hrad s hs] at hh
      apply hh.trans
      dsimp [CY]
      gcongr <;> linarith
    have hdeq : ∀ᵐ s ∂volume.restrict (Icc (S.r p.1 p.2) L), deriv dm s =
        -(‖y s‖ ^ 2 / s) * dm s + ((Qr s ^ 2 - qStar ^ 2) / (2 * s ^ 2) +
          gs s * (starRingEnd ℂ (yStar s) * (y s - yStar s)).re + gs s / 2 * ‖y s - yStar s‖ ^ 2) :=
              by
      rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hdstatic := hmsd s ⟨(hρ.1.trans hp.2.1).trans_lt hs.1, hs.2⟩
      have hdD := (hmd s hs).sub hdstatic
      rw [show deriv dm s = _ from hdD.deriv]
      dsimp [dm, mr, Qr, gs, y]
      linear_combination mass_difference_algebra s (S.m p.1 (inv s)) (mStar s)
        (S.Q p.1 (inv s)) qStar 1 (S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)) (yStar s)
    have hresult := hmass L₀ (S.r p.1 p.2) L epsilon eta Nphi Nm qStar dm gs Qr y yStar
      hL₀ (hρ.1.trans hp.2.1) hp.2.2 he he1 heta heta1 hNp hNm hq hD hy
      (hys.mono hinterval) hgs hQr henergy hbd
      (fun s hs => ⟨(hstatic s (hinterval hs)).2.1, (hstatic s (hinterval hs)).2.2,
        hcharged (p.1, inv s) (hpath (inv s) (hmem s))⟩) hY hdeq
    simpa only [dm, mr, hleft, massComparison, Real.norm_eq_abs] using hresult
  have hscalarerror : (Ct + 4) * epsilon + 96 * (Ce * eta) ≤ error := by
    dsimp [error, CB, CE]
    nlinarith only [mul_nonneg hCbM.le he, mul_nonneg hCeM.le heta]
  have hmasserror : CbM * epsilon + CeM * eta ≤ error := by
    dsimp [error, CB, CE]
    nlinarith only [mul_nonneg hCt he, mul_nonneg hCe heta, he]
  constructor
  · apply hpolyS.trans
    have hneutral : 64 * (Cn * (Nphi + Nm)) / L₀ ≤ (c / L₀) * (Nphi + Nm) := by
      calc
        _ = (64 * Cn / L₀) * (Nphi + Nm) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by dsimp [c]; linarith only [hCnM]) hL₀p.le)
          (add_nonneg hNp hNm)
    linarith only [hscalarerror, hneutral]
  · apply hpolyM.trans
    apply add_le_add (add_le_add (add_le_add
      (div_le_div_of_nonneg_right hmasserror hL₀p.le) ?_) ?_) ?_
    all_goals
      apply mul_le_mul_of_nonneg_right
      · apply div_le_div_of_nonneg_right
        · dsimp [c]; linarith only [hCn]
        · positivity
      · positivity


/-- [internal]
The outer comparison from raw normalized component equations and smooth static
reference data. Source, charge, transport, radial mass and both stopped regional
polynomials are proved by the preceding nodes and discharged here. The cutoff
and final mass coefficient depend only on the universal static bound; boundary,
electric and charge coefficients are selected next, before all solution data.
The conclusion concerns the entire given region and invokes no PDE extension. -/
theorem outer_comparison_of_normalization (Kstatic : ℝ) (hKs : 0 ≤ Kstatic) :
    ∃ Lmin Cm : ℝ, 0 < Lmin ∧ 0 < Cm ∧ ∀ Ct Bboundary : ℝ,
    0 ≤ Ct → 0 ≤ Bboundary → ∃ CB CE Cq : ℝ, 0 < CB ∧ 0 < CE ∧ 0 < Cq ∧
    ∀ (S : Fields) (D : Set (ℝ × ℝ)) (H P : ℂ) (phiStar yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b L₀ L epsilon eta qStar e : ℝ),
    let R := sidewaysTruncation S D a b L₀ L
    let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
    Lmin ≤ L₀ → L₀ ≤ L → 0 ≤ epsilon → epsilon ≤ 1 → 0 ≤ eta → eta ≤ 1 →
    4 * (CB * epsilon + CE * eta) ≤ 1 / 2 → Cq * eta ≤ 1 → |qStar| ≤ 1 →
    |e| * L * (1 + ‖H‖) = eta → IsCompact R →
    (ContinuousOn (Function.uncurry S.r) R ∧ ContinuousOn (Function.uncurry S.nu) R ∧
      ContinuousOn (Function.uncurry S.lam) R ∧ ContinuousOn (Function.uncurry S.A) R ∧
      ContinuousOn (Function.uncurry S.phi) R ∧ ContinuousOn (Function.uncurry S.theta) R ∧
      ContinuousOn (Function.uncurry S.m) R ∧ ContinuousOn (Function.uncurry S.Q) R) →
    AbsolutelyContinuousOnInterval mStar L₀ L →
    ContinuousOn phiStar (Icc L₀ L) → ContinuousOn yStar (Icc L₀ L) →
    phiStar L = P / (L : ℂ) → phiStar L + yStar L = 0 →
    (∀ s ∈ Icc L₀ L,
      HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r) (phiStar s + yStar s) s ∧
      HasDerivAt (fun r => phiStar r + yStar r) ((-ks s / s : ℝ) * yStar s) s ∧
      HasDerivAt mStar ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s) →
    (∀ s ∈ Icc L₀ L, |mStar s| ≤ 2 ∧ ‖yStar s‖ ≤ Kstatic / s ∧
      |1 - 2 * mStar s / s| ≤ 2 ∧ ‖(s : ℂ) * phiStar s‖ ≤ Kstatic ∧
      ‖phiStar s + yStar s‖ ≤ Kstatic / s ^ 2 ∧ 1 / 2 ≤ 1 - 2 * mStar s / s) →
    (∃ p ∈ R, S.r p.1 p.2 = L) → (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) →
    (∀ p ∈ R, S.nu p.1 p.2 ∈ Icc (-(1 / 2)) (-(1 / 8)) ∧
      S.lam p.1 p.2 ∈ Icc (1 / 8) (1 / 2) ∧ S.m p.1 p.2 ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2) →
    (∀ p ∈ R, HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1 ∧
      HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧ HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2 ∧
      HasDerivAt (S.phi p.1) (S.phiV p.1 p.2) p.2 ∧
      HasDerivAt (S.Q p.1) (S.QV e p.1 p.2) p.2 ∧ HasDerivAt (S.A p.1) (S.AV p.1 p.2) p.2 ∧
      HasDerivAt (fun u => S.lam u p.2) (S.rUV p.1 p.2) p.1 ∧
      HasDerivAt (fun u => S.phi u p.2) (S.phiU e p.1 p.2) p.1 ∧
      HasDerivAt (fun u => S.theta u p.2) (S.thetaU e p.1 p.2) p.1) →
    (∀ t, (t, t) ∈ R → S.r t t = L ∧ S.lam t t = 1 / 2 ∧
      ‖S.phi t t - H - P / (L : ℂ)‖ ≤ Ct * epsilon / L ∧ ‖S.a t t - H‖ ≤ epsilon / L ∧
      |massComparison S mStar t t| ≤ Ct * epsilon / L ∧ S.A t t = 0 ∧
      |S.Q t t - qStar| ≤ Bboundary * eta) →
    comparisonNorm R (scalarComparison S H phiStar) ≤ ENNReal.ofReal (4 * (CB * epsilon + CE * eta))
        ∧
      comparisonNorm R (massComparison S mStar) ≤ ENNReal.ofReal (Cm * (CB * epsilon + CE * eta) /
          L₀) := by
  obtain ⟨Cp, Cn, hCp, hCn, hsources⟩ := outer_sources_of_normalization Kstatic hKs
  obtain ⟨Lcore, Cm, hLcore, hCm, hcore⟩ := outer_comparison_of_source_envelope Kstatic Cn hKs
      hCn.le
  refine ⟨max Lcore 1, Cm, lt_of_lt_of_le hLcore (le_max_left _ _), hCm, ?_⟩
  intro Ct Bboundary hCt hB
  obtain ⟨Cq, Ce, hCq, hCe, hsources⟩ := hsources Bboundary hB
  obtain ⟨CB, CE, hCB, hCE, hcore⟩ := hcore Ct Ce Cq hCt hCe.le hCq.le
  refine ⟨CB, CE, Cq, hCB, hCE, hCq, ?_⟩
  intro S D H P phiStar yStar mStar a b L₀ L epsilon eta qStar e
  dsimp only
  intro hL hLL he he1 heta heta1 hsmall hchargedSmall hq hscale hcompact hfields hms hps hys hpsL
      hysL
    hstaticD hstatic hbase htriangle hbox hd hboundary
  rcases hfields with ⟨hr, hnuc, hlamc, hAc, hphic, htheta, hm, hQ⟩
  let R := sidewaysTruncation S D a b L₀ L
  let ks := fun r => (2 * mStar r / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar r / r)
  let wV := fun u v => (S.lam u v : ℂ) *
    (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v
  let source := fun u v =>
    let k := (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v);
    -(((-S.nu u v) * S.lam u v * k / S.r u v ^ 2 : ℝ) : ℂ) * scalarComparison S H phiStar u v +
    (((-S.nu u v) * S.lam u v / S.r u v : ℝ) : ℂ) * yStar (S.r u v) * ((k - ks (S.r u v) : ℝ) : ℂ) -
    I * ((e * S.A u v * S.lam u v : ℝ) : ℂ) * (H + (phiStar (S.r u v) + yStar (S.r u v))) +
    I * ((e * (-S.nu u v) * S.lam u v * S.Q u v / ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) : ℂ) *
      (shiftedRphi S H u v + (S.r u v : ℂ) * H)
  have hL₀ : 1 ≤ L₀ := (le_max_right Lcore 1).trans hL
  have hL₀p : 0 < L₀ := zero_lt_one.trans_le hL₀
  have hmsc : ContinuousOn mStar (Icc L₀ L) := by simpa only [uIcc_of_le hLL] using hms.continuousOn
  have hks : ContinuousOn ks (Icc L₀ L) := by
    have hc : ContinuousOn (fun s => 2 * mStar s / s) (Icc L₀ L) :=
      (continuousOn_const.mul hmsc).div continuousOn_id (fun s hs => (hL₀p.trans_le hs.1).ne')
    exact (hc.sub (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hL₀p.trans_le hs.1).ne'))).div (continuousOn_const.sub hc)
      (fun s hs => by linarith only [(hstatic s hs).2.2.2.2.2])
  have hsub {ρ : ℝ} (hρ : L₀ ≤ ρ) := sidewaysTruncation_mono_radius S D a b L hρ
  have hrin (p) (hp : p ∈ R) := (hd p hp).1
  have hrout (p) (hp : p ∈ R) := (hd p hp).2.1
  have hmout (p) (hp : p ∈ R) := (hd p hp).2.2.1
  have htri {ρ : ℝ} (hρ : L₀ ≤ ρ) := subtriangle_mem_larger_radius_of_normalization hr htriangle
      hrin hrout
    (fun p hp => by linarith only [(hbox p hp).1.2])
    (fun p hp => by linarith only [(hbox p hp).2.1.1]) ρ hρ
  have hmass4 (p) (hp : p ∈ R) : ‖massComparison S mStar p.1 p.2‖ ≤ 4 := by
    change ‖S.m p.1 p.2 - mStar (S.r p.1 p.2)‖ ≤ 4
    apply (norm_sub_le _ _).trans
    rw [Real.norm_eq_abs, abs_of_nonneg (hbox p hp).2.2.1.1, Real.norm_eq_abs]
    linarith only [(hbox p hp).2.2.1.2, (hstatic (S.r p.1 p.2) hp.2).1]
  have hpoint {E : Type} [NormedAddCommGroup E] {f : ℝ → ℝ → E} {N : ℝ} {ρ : ℝ}
      (hN : 0 ≤ N) (hb : comparisonNorm (sidewaysTruncation S D a b ρ L) f ≤ ENNReal.ofReal N) :
      ∀ p ∈ sidewaysTruncation S D a b ρ L, ‖f p.1 p.2‖ ≤ N :=
    fun p hp => norm_le_of_comparisonNorm_le hN hp hb
  have hregional (ρ) (hρ : ρ ∈ Icc L₀ L) (Nphi Nm : ℝ) (hNp : 0 ≤ Nphi) (hstop : Nphi ≤ 1)
      (hNm : 0 ≤ Nm) (hw : ∀ p ∈ sidewaysTruncation S D a b ρ L, ‖scalarComparison S H phiStar p.1
          p.2‖ ≤ Nphi)
      (hmb : ∀ p ∈ sidewaysTruncation S D a b ρ L, ‖massComparison S mStar p.1 p.2‖ ≤ Nm) :=
    hsources S D e eta a b ρ L qStar Nphi Nm H phiStar yStar mStar
      (hL₀.trans hρ.1) hρ.2 heta hq hscale hchargedSmall hNp hstop hNm hw hmb
      (fun p hp => by
        have hst := hstatic (S.r p.1 p.2) (hsub hρ.1 hp).2
        exact ⟨hst.2.2.2.1, hst.2.1, hst.2.2.2.2.1, hst.2.2.2.2.2⟩)
      (htri hρ.1) (hr.mono (hsub hρ.1)) (hlamc.mono (hsub hρ.1)) (hnuc.mono (hsub hρ.1))
      (hm.mono (hsub hρ.1)) (hQ.mono (hsub hρ.1)) (hAc.mono (hsub hρ.1))
      (hphic.mono (hsub hρ.1)) (htheta.mono (hsub hρ.1))
      (fun p hp => by
        have hh := hbox p (hsub hρ.1 hp)
        exact ⟨by linarith only [hh.2.1.1], hh.2.1.2, ⟨hh.1.1, by linarith only [hh.1.2]⟩, hh.2.2⟩)
      (fun p hp t ht => by
        have hh := hd (p.1, t) (hsub hρ.1 ((sidewaysTruncation_paths (htri hρ.1 p hp)).2 t
            (Ioo_subset_Icc_self ht)))
        exact ⟨hh.2.1, hh.2.2.2.1, hh.2.2.2.2.1, hh.2.2.1, hh.2.2.2.2.2.1⟩)
      (fun t ht => ⟨(hboundary t (hsub hρ.1 ht)).1,
        (hboundary t (hsub hρ.1 ht)).2.2.2.2.2.1, (hboundary t (hsub hρ.1 ht)).2.2.2.2.2.2⟩)
  apply hcore S D H phiStar yStar mStar ks a b L₀ L epsilon eta qStar e wV source (fun u v => e *
      S.A u v)
    ((le_max_left Lcore 1).trans hL) hLL he he1 heta heta1 hsmall hq hcompact hr hnuc hlamc hAc
        hphic htheta hm hQ
    hms hps hys hks (fun s hs => (hstaticD s hs).1) (fun s hs => (hstaticD s hs).2.1)
    (fun s hs => (hstaticD s (Ioo_subset_Icc_self hs)).2.2)
    (fun s hs => ⟨(hstatic s hs).1, (hstatic s hs).2.1, (hstatic s hs).2.2.1⟩)
    hbase htriangle hrin hrout hmout (fun p hp => (hd p hp).2.2.2.2.2.2.1)
    (fun p hp => (hd p hp).2.2.2.2.2.2.2.1) (fun p hp => (hd p hp).2.2.2.2.2.2.2.2)
    (fun p hp => (hd p hp).2.2.2.1) rfl rfl rfl
    (fun p hp => ⟨(hbox p hp).1.2, (hbox p hp).2.1.1, (hbox p hp).2.2⟩)
    (fun t ht => by
      have hb := hboundary t ht
      have hb' := outer_boundary_difference_data_of_normalization S H P phiStar yStar
        (hL₀p.trans_le hLL) hb.1 hb.2.1 hpsL hysL hb.2.2.1 hb.2.2.2.1
      refine ⟨hb.1, hb'.1, ?_, hb.2.2.2.2.1⟩
      dsimp only [wV]
      rw [hb'.2.1]
      exact hb'.2.2)
  · intro ρ hρ hstop p hp
    have h := hregional ρ hρ 1 4 (by norm_num) le_rfl (by norm_num)
      (hpoint (by norm_num : (0 : ℝ) ≤ 1) (by simpa only [ENNReal.ofReal_one] using hstop))
      (fun p hp => hmass4 p (hsub hρ.1 hp)) p hp
    exact ⟨h.2.1, h.1⟩
  · intro ρ hρ Nphi Nm hNp hNm hstop hw hmb p hp
    exact (hregional ρ hρ Nphi Nm hNp hstop hNm (hpoint hNp hw) (hpoint hNm hmb) p hp).2.2

end Observation

end EmcsfAcExtension.Global
