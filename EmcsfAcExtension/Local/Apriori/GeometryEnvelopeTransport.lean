module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeRegular
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseEndpoint
import EmcsfAcExtension.Local.Calculus.Geometric
import EmcsfAcExtension.Local.Calculus.GeometricAxis

/-! # Endpoint transport bounds for the geometric derivatives

The real common source is integrated before taking an envelope. Continuity
of the transported derivative, rather than source integrability at the
axis, supplies the endpoint limit (`charged_SF_new_version.tex:L4888–L4894`).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- A real characteristic derivative with continuous primitive up to both
endpoints has modulus bounded by its boundary modulus and the absolute
source integral. The exact coefficients are one, uniformly in all
functions and intervals; the nonnegative source integral may be infinite. -/
theorem real_transport_enorm_le {a b : ℝ} {g q : ℝ → ℝ} (hab : a < b)
    (cg : ContinuousOn g (Icc a b)) (cq : ContinuousOn q (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt g (q x) x) :
    ‖g b‖ₑ ≤ ‖g a‖ₑ + ∫⁻ x in Icc a b, ‖q x‖ₑ := by
  have hn (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  have hb := characteristic_transport_enorm_le_of_interior
    (g := fun x => (g x : ℂ)) (c := fun _ => 0) (q := fun x => (q x : ℂ))
    hab (by norm_num : (0 : ℝ) ≤ 1)
    (Complex.continuous_ofReal.comp_continuousOn cg) continuousOn_const
    (Complex.continuous_ofReal.comp_continuousOn cq)
    (fun x hx => by simpa only [zero_mul, zero_add] using (hd x hx).ofReal_comp)
    (by intro d t hd hdt htb x hx; simp)
  simpa only [ENNReal.ofReal_one, one_mul, hn] using hb

/-- Each outgoing geometric derivative is bounded by its initial value
plus the entire incoming source section at that label. The coefficients
are exactly one, uniformly in all solution and derivative parameters. -/
theorem geomL_characteristic_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖geomL (triangle 0 T) S u v‖ₑ ≤ ‖geomL (triangle 0 T) S 0 v‖ₑ +
      ∫⁻ x in Icc 0 v, ‖geomSource S x v‖ₑ := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · exact le_add_right le_rfl
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 u) (triangle 0 T) :=
    fun x hx => ⟨hx.1, hx.2.trans huv, hvT⟩
  have cs := continuousOn_geomSource_off_axis hset.pos hset.c1
  have cq : ContinuousOn (fun x => geomSource S x v) (Ioo 0 u) :=
    cs.comp (f := fun x : ℝ => (x, v)) (continuous_id.prodMk continuous_const).continuousOn
      (fun x hx => ⟨hs ⟨hx.1.le, hx.2.le⟩, hx.2.trans_le huv⟩)
  have hd (x : ℝ) (hx : x ∈ Ioo 0 u) :
      HasDerivAt (fun x => geomL (triangle 0 T) S x v) (geomSource S x v) x :=
    (bv_geom_trans_out hset.c1 hx.1.le (hx.2.trans_le huv) hvT).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le huv))
  have hb := real_transport_enorm_le hu
    ((continuousOn_geomL hset.pos hset.c1).comp
      (continuous_id.prodMk continuous_const).continuousOn hs) cq hd
  change ‖geomL (triangle 0 T) S u v‖ₑ ≤
    ‖geomL (triangle 0 T) S 0 v‖ₑ + ∫⁻ x in Icc 0 u, ‖geomSource S x v‖ₑ at hb
  exact hb.trans (add_le_add le_rfl (lintegral_mono_set (Icc_subset_Icc le_rfl huv)))

/-- Each incoming geometric derivative is bounded by the common geometric
axis value plus its outgoing source section. The exact coefficients are
one and no smallness or source-integrability premise is required. -/
theorem geomN_characteristic_bound {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖geomN (triangle 0 T) S u v‖ₑ ≤ ‖geomL (triangle 0 T) S u u‖ₑ +
      ∫⁻ x in Icc u T, ‖geomSource S u x‖ₑ := by
  have huT : u ∈ Icc 0 T := ⟨hu, huv.trans hvT⟩
  have ha := (Area.smooth_geometric_axis_match hset.pos hset.c1 huT).1
  rcases eq_or_lt_of_le huv with rfl | huv
  · rw [ha]
    exact le_add_right le_rfl
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have cs := continuousOn_geomSource_off_axis hset.pos hset.c1
  have cq : ContinuousOn (fun x => geomSource S u x) (Ioo u v) :=
    cs.comp (f := fun x : ℝ => (u, x)) (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx => ⟨hs ⟨hx.1.le, hx.2.le⟩, hx.1⟩)
  have hd (x : ℝ) (hx : x ∈ Ioo u v) :
      HasDerivAt (fun x => geomN (triangle 0 T) S u x) (geomSource S u x) x :=
    (bv_geom_trans_in hset.c1 hu hx.1 (hx.2.le.trans hvT)).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le hvT))
  have hb := real_transport_enorm_le huv
    ((continuousOn_geomN hset.pos hset.c1).comp
      (continuous_const.prodMk continuous_id).continuousOn hs) cq hd
  change ‖geomN (triangle 0 T) S u v‖ₑ ≤
    ‖geomN (triangle 0 T) S u u‖ₑ + ∫⁻ x in Icc u v, ‖geomSource S u x‖ₑ at hb
  rw [← ha] at hb
  exact hb.trans (add_le_add le_rfl (lintegral_mono_set (Icc_subset_Icc le_rfl hvT)))

end EmcsfAcExtension.Local
