module

public import EmcsfAcExtension.Local.Limit.AcBridgeScalarBounds
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Infra.Mixed.SectionIntegral

/-! # Uniform primary and ordinary scalar limits for broad AC comparisons

This is the common analytic passage of internal project record item 7.5. Every bound is
uniform in the section label; no derivative supremum is used.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- A uniformly vanishing real error bound gives uniform convergence.
The coefficient `K` is explicit and can depend on fixed parameters of this
qualitative helper; no coefficient is selected by choice. -/
theorem uniform_tendsto_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {Fn : ℕ → ℝ → ℝ → E} {f : ℝ → ℝ → E}
    {d : ℕ → ℝ} (K : ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hb : ∀ n p, p ∈ D → ‖Fn n p.1 p.2 - f p.1 p.2‖ ≤ K * d n) :
    TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop D := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ρ hρ
  have ht : Tendsto (fun n => K * d n) atTop (𝓝 0) := by simpa using hd.const_mul K
  filter_upwards [(tendsto_order.1 ht).2 ρ hρ] with n hn p hp
  simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using (hb n p hp).trans_lt hn

/-- Pass broad AC pair comparisons to uniform limits of the expansions,
radius, scalar, normalized fields and potential. The original common size
bounds the potential coefficient by `6*C*|e|*T*M`. The explicit radius factor
is `Cb*T`; neither factor is absorbed into a universal constant. -/
theorem ac_uniform_limits_of_comparisons {T e c Cb η M C : ℝ}
    {hn : ℕ → ℝ → ℂ} {h : ℝ → ℂ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hc : 0 < c) (hC : 0 < C)
    (hSn : ∀ n, IsSolution e (Sn n) (triangle 0 T))
    (hS : IsSolution e S (triangle 0 T))
    (hbox : ∀ n, StabBox (Sn n) c Cb η M (triangle 0 T))
    (hMn : ∀ n, datumM (hn n) T ≤ 3 * M) (hM : datumM h T ≤ 3 * M)
    (hp : ∀ n, StabConclusion C e T (hn n) h (Sn n) S ∧
      supDist T (Sn n).A S.A ≤ ENNReal.ofReal
        (C * |e| * T * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T))
    (hd : Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).lam) (Function.uncurry S.lam) atTop
        (triangle 0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).nu) (Function.uncurry S.nu) atTop (triangle
        0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).r) (Function.uncurry S.r) atTop (triangle 0
        T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).a) (Function.uncurry S.a) atTop (triangle 0
        T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).b) (Function.uncurry S.b) atTop (triangle 0
        T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi) (Function.uncurry S.phi) atTop
        (triangle 0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).A) (Function.uncurry S.A) atTop (triangle 0
        T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).theta) (Function.uncurry S.theta) atTop
        (triangle 0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).xi) (Function.uncurry S.xi) atTop (triangle
        0 T) := by
  have hCb : 0 ≤ Cb := by
    have hh := (hbox 0).2 (0, 0) ⟨le_rfl, le_rfl, hT.le⟩
    exact hc.le.trans (hh.1.trans hh.2.1)
  have hrad n (p : ℝ × ℝ) (hp' : p ∈ triangle 0 T) :
      0 ≤ (Sn n).r p.1 p.2 ∧ (Sn n).r p.1 p.2 ≤ Cb * T := by
    have hs : outSeg p.1 p.1 p.2 ⊆ triangle 0 T := by
      rintro ⟨u,v⟩ ⟨rfl, hv⟩
      exact ⟨hp'.1, hv.1, hv.2.trans hp'.2.2⟩
    have hn0 : 0 ≤ (Sn n).r p.1 p.2 := by
      rcases hp'.2.1.eq_or_lt with he | hl
      · simp only [← he, ((hSn n).axis p.1 ⟨hp'.1, le_rfl, he.trans_le hp'.2.2⟩).1, le_refl]
      · exact ((hSn n).r_pos p hp' hl).le
    refine ⟨hn0, (Broad.outgoing_radius_upper (hSn n) hp'.2.1 hs
      (fun v hv => ((hbox n).2 (p.1, v) (hs ⟨rfl, hv⟩)).2.1)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left (by linarith only [hp'.1, hp'.2.2]) hCb
  have hb n (p : ℝ × ℝ) (hp' : p ∈ triangle 0 T) := (hp n).1.pointwise_of_stability hT.le p hp'
  have hparts n (p : ℝ × ℝ) (hp' : p ∈ triangle 0 T) :
      |(Sn n).lam p.1 p.2 - S.lam p.1 p.2| ≤ C * dataDist (hn n) h T ∧
      |(Sn n).nu p.1 p.2 - S.nu p.1 p.2| ≤ C * dataDist (hn n) h T ∧
      |(Sn n).r p.1 p.2 - S.r p.1 p.2| / (Sn n).r p.1 p.2 ≤ C * dataDist (hn n) h T ∧
      ‖(Sn n).a p.1 p.2 - S.a p.1 p.2‖ ≤ C * dataDist (hn n) h T ∧
      ‖(Sn n).b p.1 p.2 - S.b p.1 p.2‖ ≤ C * dataDist (hn n) h T ∧
      ‖(Sn n).phi p.1 p.2 - S.phi p.1 p.2‖ ≤ C * dataDist (hn n) h T := by
    have hh := hb n p hp'
    have hz := div_nonneg (abs_nonneg ((Sn n).r p.1 p.2 - S.r p.1 p.2)) (hrad n p hp').1
    have hl := abs_nonneg ((Sn n).lam p.1 p.2 - S.lam p.1 p.2)
    have hnu := abs_nonneg ((Sn n).nu p.1 p.2 - S.nu p.1 p.2)
    have ha := norm_nonneg ((Sn n).a p.1 p.2 - S.a p.1 p.2)
    have hbb := norm_nonneg ((Sn n).b p.1 p.2 - S.b p.1 p.2)
    have hphi := norm_nonneg ((Sn n).phi p.1 p.2 - S.phi p.1 p.2)
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hl := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).lam) (f :=
      S.lam) C hd
    (fun n p hp' => by simpa only [Real.norm_eq_abs] using (hparts n p hp').1)
  have hnu := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).nu) (f :=
      S.nu) C hd
    (fun n p hp' => by simpa only [Real.norm_eq_abs] using (hparts n p hp').2.1)
  have ha := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).a) (f := S.a)
      C hd (fun n p hp' => (hparts n p hp').2.2.2.1)
  have hb' := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).b) (f :=
      S.b) C hd (fun n p hp' => (hparts n p hp').2.2.2.2.1)
  have hphi := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).phi) (f :=
      S.phi) C hd (fun n p hp' => (hparts n p hp').2.2.2.2.2)
  have hr := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).r) (f := S.r)
      (C * (Cb * T)) hd (fun n p hp' => by
    rw [Real.norm_eq_abs]
    rcases hp'.2.1.eq_or_lt with he | hlt
    · rw [← he, ((hSn n).axis p.1 ⟨hp'.1, le_rfl, he.trans_le hp'.2.2⟩).1,
        (hS.axis p.1 ⟨hp'.1, le_rfl, he.trans_le hp'.2.2⟩).1]
      simp only [sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hC.le (mul_nonneg hCb hT.le))
        (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)
    · have hh := (div_le_iff₀ ((hSn n).r_pos p hp' hlt)).1 (hparts n p hp').2.2.1
      calc
        _ ≤ (C * dataDist (hn n) h T) * (Sn n).r p.1 p.2 := hh
        _ ≤ (C * dataDist (hn n) h T) * (Cb * T) := mul_le_mul_of_nonneg_left (hrad n p hp').2
          (mul_nonneg hC.le (add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg))
        _ = _ := by ring)
  have hA := uniform_tendsto_of_norm_sub_le (D := triangle 0 T) (Fn := fun n => (Sn n).A) (f := S.A)
      (6 * C * |e| * T * M) hd (fun n p hp' => by
    have hdn : 0 ≤ dataDist (hn n) h T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
    have hsize : 2 * max (datumM (hn n) T) (datumM h T) ≤ 6 * M := by
      have := max_le (hMn n) hM
      linarith
    have hsz0 : 0 ≤ 2 * max (datumM (hn n) T) (datumM h T) := by
      have hv : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
      have hh : 0 ≤ datumM h T := by unfold datumM; positivity
      exact mul_nonneg (by norm_num) (hh.trans (le_max_right _ _))
    have hnonneg : 0 ≤ C * |e| * T * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T
        := by positivity
    have hh : ‖(Sn n).A p.1 p.2 - S.A p.1 p.2‖ ≤
        C * |e| * T * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T :=
      (ENNReal.ofReal_le_ofReal_iff hnonneg).1 (by
      simpa only [ofReal_norm] using (le_iSup₂ p hp').trans (hp n).2)
    calc
      _ ≤ C * |e| * T * (2 * max (datumM (hn n) T) (datumM h T)) * dataDist (hn n) h T := hh
      _ ≤ C * |e| * T * (6 * M) * dataDist (hn n) h T := by gcongr
      _ = _ := by ring)
  have cna n := (hSn n).cont_phi.add ((hSn n).cont_theta.div
    (Complex.continuous_ofReal.comp_continuousOn (hSn n).cont_lam)
    (fun p hp' => Complex.ofReal_ne_zero.mpr ((hSn n).lam_pos p hp').ne'))
  have cnb n := (hSn n).cont_phi.add ((hSn n).cont_xi.div
    (Complex.continuous_ofReal.comp_continuousOn (hSn n).cont_nu)
    (fun p hp' => Complex.ofReal_ne_zero.mpr ((hSn n).nu_neg p hp').ne))
  have hθ := Mixed.tendstoUniformlyOn_mul_of_isCompact (isCompact_triangle 0 T)
    (fun n => Complex.continuous_ofReal.comp_continuousOn (hSn n).cont_lam)
    (fun n => (cna n).sub (hSn n).cont_phi)
    (Complex.isometry_ofReal.uniformContinuous.comp_tendstoUniformlyOn hl) (ha.sub hphi)
  have hξ := Mixed.tendstoUniformlyOn_mul_of_isCompact (isCompact_triangle 0 T)
    (fun n => Complex.continuous_ofReal.comp_continuousOn (hSn n).cont_nu)
    (fun n => (cnb n).sub (hSn n).cont_phi)
    (Complex.isometry_ofReal.uniformContinuous.comp_tendstoUniformlyOn hnu) (hb'.sub hphi)
  have hθeq (F : Fields) (hF : IsSolution e F (triangle 0 T)) (p : ℝ × ℝ) (hp' : p ∈ triangle 0 T) :
      (F.lam p.1 p.2 : ℂ) * (F.a p.1 p.2 - F.phi p.1 p.2) = F.theta p.1 p.2 := by
    simp only [Fields.a, add_sub_cancel_left]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hF.lam_pos p hp').ne')
  have hξeq (F : Fields) (hF : IsSolution e F (triangle 0 T)) (p : ℝ × ℝ) (hp' : p ∈ triangle 0 T) :
      (F.nu p.1 p.2 : ℂ) * (F.b p.1 p.2 - F.phi p.1 p.2) = F.xi p.1 p.2 := by
    simp only [Fields.b, add_sub_cancel_left]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (hF.nu_neg p hp').ne)
  refine ⟨hl, hnu, hr, ha, hb', hphi, hA, ?_, ?_⟩
  · exact (hθ.congr (Eventually.of_forall fun n p hp' => hθeq _ (hSn n) p hp')).congr_right (fun p
      hp' => hθeq _ hS p hp')
  · exact (hξ.congr (Eventually.of_forall fun n p hp' => hξeq _ (hSn n) p hp')).congr_right (fun p
      hp' => hξeq _ hS p hp')

end EmcsfAcExtension.Local
