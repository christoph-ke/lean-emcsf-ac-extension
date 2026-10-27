module

public import EmcsfAcExtension.Local.Limit.Construct2Strong
import EmcsfAcExtension.Local.Limit.Construct2GeometryAC
import EmcsfAcExtension.Local.Limit.ExistencePointwise
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Apriori.Bootstrap
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Local.Limit.ScalarAxisAC
import EmcsfAcExtension.Infra.W11.Distance

/-! # Controlled strong approximants for AC restart data

The construction uses the two authorized producer propositions and the landed
smooth a priori theorem. A common tail is classical, admissible for comparison,
and carries the a priori bounds at its own actual datum variation.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Produce a strong approximation with the original-data variation retained
in the a priori limit. All three positive constants are universal, before
triangle, coupling and datum. The comparison size and thresholds are auxiliary
and all premises are discharged from the two authorized producer contracts.
This constructs the frozen strong-limit witness, without asserting solution
membership or the final existence-bound bundle. -/
theorem Null.controlled_strong_approximants_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt) :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (S : Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧
          (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          (∀ n, SmoothBounds C e T (datumVar (hn n) T) (datumM (hn n) T) (Sn n)) ∧
          StrongLimit e T Sn S ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mu)
            (Function.uncurry S.mu) atTop (triangle 0 T) ∧
          (∀ p ∈ triangle 0 T, 1 / 4 ≤ S.lam p.1 p.2 ∧ 1 / 4 ≤ -S.nu p.1 p.2 ∧
            (p.2 - p.1) / 4 ≤ S.r p.1 p.2 ∧ 1 / 4 ≤ 1 - S.mu p.1 p.2) ∧
          (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
          (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
          AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
          UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.lam u) u T) ∧
          (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v) := by
  obtain ⟨η, hη, hstrong⟩ := Null.strong_limit_of_inputs hstab 1 (by norm_num)
  obtain ⟨ηg, hηg, hgeoAC⟩ := Null.geometry_natural_ac_of_inputs hstab 1 (by norm_num)
  obtain ⟨ε₀, δ₀, q, hε₀, hδ₀, _, happ⟩ :=
    Null.comparison_approximants_of_inputs hex (min η ηg) (lt_min hη hηg)
  obtain ⟨εa, δa, C, hεa, hδa, hC, hapriori⟩ := Null.smooth_apriori_box
  refine ⟨min ε₀ (εa / 2), min δ₀ (δa / 2), C,
    lt_min hε₀ (by positivity), lt_min hδ₀ (by positivity), hC, ?_⟩
  intro T e h hT hac hε hδ
  obtain ⟨hn, Sn, hs, hv, herr, hevar, hvar, hset, hsmall⟩ :=
    happ T e h hT hac (hε.trans (min_le_left _ _)) (hδ.trans (min_le_left _ _))
  have hscale : Tendsto (fun n => chargedScale e (hn n) T) atTop (𝓝 (chargedScale e h T)) := by
    unfold chargedScale datumM
    simpa only [hv, Function.comp_def] using
      ((tendsto_const_nhds.add (hvar.const_mul 10)).const_mul (|e| * (T / 2)))
  have hdε : datumVar h T < εa := by
    have hh := hε.trans (min_le_right _ _)
    linarith only [hh, hεa]
  have hdδ : chargedScale e h T < δa := by
    have hh := hδ.trans (min_le_right _ _)
    linarith only [hh, hδa]
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (((tendsto_order.1 hvar).2 εa hdε).and ((tendsto_order.1 hscale).2 δa hdδ))
  let Sn' n := Sn (n + N)
  let hn' n := hn (n + N)
  have hset' n : StabSetting e T q (2 * datumM h T) 1 (Sn' n) (hn' n) := hset _
  obtain ⟨S, hlim, hMuUniform, ha, hb, haxis, hUIj, hUIk⟩ := hstrong T e q (2 * datumM h T) Sn' hn'
      h hset' hac
    (fun n => hv _) (herr.comp (tendsto_add_atTop_nat N)) (hsmall.trans (min_le_left _ _))
  obtain ⟨hlamAC, hnuAC⟩ := hgeoAC T e q (2 * datumM h T) Sn' hn' h S hset' hac
    (fun n => hv _) (herr.comp (tendsto_add_atTop_nat N)) (hsmall.trans (min_le_right _ _)) hlim
  have hgeom := hlim.lower_geometry_of_settings hset' 
  have hR p (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S.r p.1 p.2 :=
    (div_pos (sub_pos.mpr hlt) (by norm_num)).trans_le (hgeom p hp).2.2
  have hg p (hp : p ∈ triangle 0 T) : 1 / 4 ≤ 1 - S.mu p.1 p.2 :=
    ge_of_tendsto ((hlim.tendsto_mu_of_radius_pos (fun n => (hset' n).c1) hR hp).const_sub 1)
      (Eventually.of_forall fun n => ((hset' n).box.2 p hp).2.2.2.2.1)
  refine ⟨Sn', hn', S, fun n => hs _, fun n => hv _, herr.comp (tendsto_add_atTop_nat N),
    hevar.comp (tendsto_add_atTop_nat N), hvar.comp (tendsto_add_atTop_nat N),
    fun n => ⟨(hset' n).c1, (hset' n).data⟩, ?_, hlim, hMuUniform,
    fun p hp => ⟨(hgeom p hp).1, (hgeom p hp).2.1, (hgeom p hp).2.2, hg p hp⟩, ha, hb, haxis, hUIj,
        hUIk, hlamAC, hnuAC⟩
  intro n
  exact hapriori T e (Sn' n) (hn' n) hT (hset' n).c1 (hset' n).data
    (hN _ (Nat.le_add_left _ _)).1.le (hN _ (Nat.le_add_left _ _)).2.le

/-- Recover the exact initial radius, normalized datum and axis gauge from
a classical strong approximation. Coefficients are one, uniformly in the
triangle and datum; the datum convergence uses its actual finite variation. -/
theorem restart_data_of_strongLimit {T e : ℝ} {Sn : ℕ → Fields} {hn : ℕ → ℝ → ℂ}
    {S : Fields} {h : ℝ → ℂ} (hT : 0 < T)
    (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hdata : ∀ n, IsRestartData (Sn n) (hn n) T)
    (hac : AbsolutelyContinuousOnInterval h 0 T)
    (hvertex : ∀ n, hn n 0 = h 0)
    (hvar : Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0))
    (hlim : StrongLimit e T Sn S)
    (hL : ∀ p ∈ triangle 0 T, S.lam p.1 p.2 ≠ 0) : IsRestartData S h T := by
  have hdatum n : AbsolutelyContinuousOnInterval (hn n) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT.le]
    exact ((hc1 n).c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)).congr
        (fun v hv => (hdata n).1 v hv |>.2.symm)
  constructor
  · intro v hv
    have hp : ((0 : ℝ), v) ∈ triangle 0 T := ⟨le_rfl, hv.1, hv.2⟩
    constructor
    · exact tendsto_nhds_unique (hlim.unif_r.tendsto_at hp)
        (by simpa only [Function.uncurry_apply_pair, fun n => ((hdata n).1 v hv).1] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => v / 2) atTop (𝓝 (v / 2))))
    · have hhn : Tendsto (fun n => hn n v) atTop (𝓝 (h v)) := by
        apply tendsto_iff_norm_sub_tendsto_zero.2
        apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hvar
        have hb := W11.norm_sub_le_intervalDist ((hdatum n).boundedVariationOn_Icc hT.le)
          (hac.boundedVariationOn_Icc hT.le) hv
        simpa only [W11.intervalDist_zero, hvertex, sub_self, norm_zero, zero_add] using hb
      exact tendsto_nhds_unique (hlim.tendsto_a_of_lam_ne_zero hp (hL _ hp))
        (by simpa only [fun n => ((hdata n).1 v hv).2] using hhn)
  · intro t ht
    have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
    exact tendsto_nhds_unique (hlim.unif_A.tendsto_at hp)
      (by simpa only [Function.uncurry_apply_pair, fun n => (hdata n).2 t ht] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))

end EmcsfAcExtension.Local
