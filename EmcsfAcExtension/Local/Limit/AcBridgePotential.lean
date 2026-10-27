module

public import EmcsfAcExtension.Local.Limit.Inputs
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Local.Limit.AcBridgeDerivative
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Limit.AcBridgeStrongSequence
import EmcsfAcExtension.Local.Stability.GeomStrongACSections
import EmcsfAcExtension.Local.Broad.GeometryContinuity
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Full general-AC strong potential characteristic record

Incoming AC follows from the smooth differentiated radial integral and its
triangular difference estimate, passed through strong construction limits.
Its ordinary derivative is integrable and may be unbounded pointwise.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing potential equation identifies the ordinary derivative a.e.
on every complete broad section. The axis may be exceptional, and no
pointwise derivative bound or smoothness is asserted. -/
theorem _root_.EmcsfAcExtension.IsSolution.potential_derivative_out_ae {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) {u : ℝ} (hu : u ∈ Icc 0 T) :
    deriv (S.A u) =ᵐ[volume.restrict (Icc u T)] S.AV u := by
  have hm : MapsTo (fun v => (u,v)) (Ioo u T) (triangle 0 T) :=
    fun v hv => ⟨hu.1,hv.1.le,hv.2.le⟩
  have sect {f : ℝ → ℝ → ℝ} (hf : ContinuousOn (Function.uncurry f) (triangle 0 T)) :
      ContinuousOn (f u) (Ioo u T) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn hm
  have cq : ContinuousOn (S.AV u) (Ioo u T) := by
    apply ((((continuousOn_const.mul (sect hS.cont_nu)).mul (sect hS.cont_lam)).mul
      (sect hS.cont_Q)).div ((continuousOn_const.sub (sect (Broad.continuousOn_mu hS))).mul
        ((sect hS.cont_r).pow 2)))
    intro v hv
    exact mul_ne_zero (hS.one_sub_mu_pos _ (hm hv)).ne'
      (pow_ne_zero 2 (hS.r_pos _ (hm hv) hv.1).ne')
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  apply HasDerivAt.deriv
  apply hasDerivAt_of_integralForm_interior hv cq
  intro a b hua hab hbT
  exact (hS.eq_out u a b hua hab (by
    rintro ⟨x,y⟩ ⟨rfl,hay,hyb⟩
    exact ⟨hu.1,hua.le.trans hay,hyb.trans hbT.le⟩)).2.2.2.2.1

/-- The actual frozen outgoing potential density is integrable up to the
regular axis and recovers the zero-gauge radial integral. Full section AC
has already been established by the strong incoming/outgoing passage. -/
theorem _root_.EmcsfAcExtension.IsSolution.potential_axis_primitive_of_ac {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) {u : ℝ} (hu : u ∈ Icc 0 T)
    (hac : AbsolutelyContinuousOnInterval (S.A u) u T) (hz : S.A u u = 0) :
    IntervalIntegrable (S.AV u) volume u T ∧
      ∀ v ∈ Icc u T, S.A u v = ∫ s in u..v, S.AV u s := by
  have hd := hS.potential_derivative_out_ae hu
  have hi : IntervalIntegrable (S.AV u) volume u T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu.2).2
      (((intervalIntegrable_iff_integrableOn_Icc_of_le hu.2).1 hac.intervalIntegrable_deriv).congr
          hd)
  refine ⟨hi,?_⟩
  intro v hv
  have hp := (stab_real_ac_section_primitive hu.2 hac).2 v hv
  rw [hz,zero_add] at hp
  apply hp.trans
  apply intervalIntegral.integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_Icc).1 hd
  filter_upwards [he] with x hx hxmem
  rw [uIoc_of_le hv.1] at hxmem
  exact hx ⟨hxmem.1.le,hxmem.2.trans hv.2⟩

/-- Full potential characteristic convergence, with the actual outgoing
constraint and the integrable incoming ordinary derivative. The latter's
primitive equality includes every endpoint and hence also gives its weak
derivative interpretation; no everywhere finite derivative is stipulated. -/
structure PotentialCharacteristicLimit (T : ℝ) (Sn : ℕ → Fields) (S : Fields) : Prop where
  /-- AC and section-uniform strong derivatives in both directions. -/
  characteristics : RealCharacteristicLimit T (fun n => (Sn n).A) S.A
  /-- Each original outgoing derivative is the frozen potential constraint. -/
  density_out : ∀ n u, u ∈ Icc 0 T →
    deriv ((Sn n).A u) =ᵐ[volume.restrict (Icc u T)] (Sn n).AV u
  /-- The limiting outgoing derivative is the frozen potential constraint. -/
  limit_density_out : ∀ u ∈ Icc 0 T,
    deriv (S.A u) =ᵐ[volume.restrict (Icc u T)] S.AV u
  /-- The original axis gauges vanish. -/
  axis_gauge : ∀ n u, u ∈ Icc 0 T → (Sn n).A u u = 0
  /-- The limiting axis gauge vanishes. -/
  limit_axis_gauge : ∀ u ∈ Icc 0 T, S.A u u = 0
  /-- Each original outgoing axis-gauge radial primitive is the literal constraint. -/
  primitive_out : ∀ n u, u ∈ Icc 0 T → IntervalIntegrable ((Sn n).AV u) volume u T ∧
    ∀ v ∈ Icc u T, (Sn n).A u v = ∫ s in u..v, (Sn n).AV u s
  /-- The limiting outgoing axis-gauge primitive includes the axis endpoint. -/
  limit_primitive_out : ∀ u ∈ Icc 0 T, IntervalIntegrable (S.AV u) volume u T ∧
    ∀ v ∈ Icc u T, S.A u v = ∫ s in u..v, S.AV u s
  /-- The incoming primitive uses the actual integrable ordinary derivative. -/
  primitive_in : ∀ n v, v ∈ Icc 0 T →
    IntervalIntegrable (deriv (fun u => (Sn n).A u v)) volume 0 v ∧
      ∀ u ∈ Icc 0 v, (Sn n).A u v = (Sn n).A 0 v +
        ∫ s in (0 : ℝ)..u, deriv (fun u => (Sn n).A u v) s
  /-- The limiting incoming derivative is integrable and recovers the field. -/
  limit_primitive_in : ∀ v ∈ Icc 0 T,
    IntervalIntegrable (deriv (fun u => S.A u v)) volume 0 v ∧
      ∀ u ∈ Icc 0 v, S.A u v = S.A 0 v + ∫ s in (0 : ℝ)..u, deriv (fun u => S.A u v) s

/-- [internal]
charged_SF_new_version.tex:L5453–L5523. The full potential record on arbitrary
regular-center AC sequences. The
positive threshold and coefficient depend only on the fixed box gap `c`
and envelope coefficient `H`, before time, coupling, size, data and solutions.
The incoming and outgoing derivative estimate retains the explicit scale
`6*C*|e|*M*T`; its stronger bound implies the approved loose `(1+σ)` form.
All original solutions are identified broadly before any derivatives are
transferred; neither smoothness nor constructed provenance is assumed. -/
theorem potential_characteristic_ac_strong_limit_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt)
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
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
          PotentialCharacteristicLimit T Sn S ∧
          (∀ n, (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
            ‖deriv ((Sn n).A u) v - deriv (S.A u) v‖ₑ) +
            (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
              ‖deriv (fun s => (Sn n).A s v) u - deriv (fun s => S.A s v) u‖ₑ) ≤
                ENNReal.ofReal (6 * C * |e| * M * T * dataDist (hn n) h T)) := by
  obtain ⟨s,C,hs,hC,hcore⟩ := ac_mass_potential_limits_of_inputs hex hstab c H hc hH
  refine ⟨s,C,hs,hC,?_⟩
  intro T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn hbox hJn hKn hjn hkn hmass hsmall hd
  obtain ⟨S,hS,hdS,_,hp,_,hb⟩ := hcore T e η M Cb hn h Sn Jn Kn hT hη hac hacn hSn hdn
    hbox hJn hKn hjn hkn hmass hsmall hd
  have prim {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) :
      IntervalIntegrable (deriv f) volume a b ∧
        ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, deriv f t :=
    ⟨hf.intervalIntegrable_deriv,(stab_real_ac_section_primitive hab hf).2⟩
  exact ⟨S,hS,hdS,⟨hp,fun n _ hu => (hSn n).potential_derivative_out_ae hu,
    fun _ hu => hS.potential_derivative_out_ae hu,fun n => (hdn n).2,hdS.2,
    fun n u hu => (hSn n).potential_axis_primitive_of_ac hu (hp.ac_out n u hu) ((hdn n).2 u hu),
    fun u hu => hS.potential_axis_primitive_of_ac hu (hp.limit_ac_out u hu) (hdS.2 u hu),
    fun n v hv => prim hv.1 (hp.ac_in n v hv),
    fun v hv => prim hv.1 (hp.limit_ac_in v hv)⟩,hb⟩

end EmcsfAcExtension.Local
