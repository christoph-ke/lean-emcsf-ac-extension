module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import EmcsfAcExtension.Local.Construction.StripPicard

/-! # Uniform continuous strips about an old lower trace

A reference cancels the incoming residual at zero strip height. Both
residuals are uniformly linear in the added height; weighted Picard then
stays in a prescribed tube. Constants are chosen before the old apex,
rectangle width, and entering traces.
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace EmcsfAcExtension.Local

variable {I O : Type*} [NormedAddCommGroup I] [NormedSpace ℝ I] [CompleteSpace I]
  [NormedAddCommGroup O] [NormedSpace ℝ O] [CompleteSpace O]

private noncomputable def stripReference (w : ℝ → I × O) (y : ℝ → I) (S : ℝ)
    (p : ℝ × ℝ) : I × O :=
  ((w p.1).1 + (y p.2-y S),(w p.1).2)

omit [CompleteSpace I] [CompleteSpace O] [NormedSpace ℝ I] [NormedSpace ℝ O] in
private theorem continuous_stripReference {w : ℝ → I × O} {y : ℝ → I} (S : ℝ)
    (hw : Continuous w) (hy : Continuous y) : Continuous (stripReference w y S) :=
  ((hw.fst.comp continuous_fst).add ((hy.comp continuous_snd).sub continuous_const)).prodMk
    (hw.snd.comp continuous_fst)

omit [CompleteSpace I] [CompleteSpace O] [NormedSpace ℝ I] [NormedSpace ℝ O] in
private theorem norm_stripReference_sub (w : ℝ → I × O) (y : ℝ → I) (S : ℝ)
    (p : ℝ × ℝ) : ‖stripReference w y S p-w p.1‖ = ‖y p.2-y S‖ := by
  simp [stripReference,Prod.norm_def]

private theorem norm_sub_le_lipschitz {E Z : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup Z] {L : ℝ≥0} {f : E → Z} (hf : LipschitzWith L f)
    (x y : E) : ‖f x-f y‖ ≤ L*‖x-y‖ := by
  simpa only [dist_eq_norm] using hf.dist_le_mul x y

omit [CompleteSpace I] [CompleteSpace O] in
private theorem strip_reference_residual_bounds {L J : ℝ≥0} {H T S d δ : ℝ}
    {fi : I × O → I} {fo : I × O → O} {w : ℝ → I × O} {y : ℝ → I}
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hd : d ∈ Icc 0 T) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo)
    (hw : Continuous w) (hy : LipschitzWith J y)
    (hold : ∀ u ∈ Icc 0 d, (w u).1 = y S + ∫ s in 0..u, fi (w s))
    (hout : ∀ u ∈ Icc 0 d, ‖fo (w u)‖ ≤ H) :
    (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
      ‖y v + (∫ s in 0..u, fi (stripReference w y S (s,v))) -
        (stripReference w y S (u,v)).1‖ ≤ (H+(L : ℝ)*(J : ℝ)+T*(L : ℝ)*(J : ℝ)+1)*δ) ∧
    (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
      ‖(w u).2 + (∫ t in S..v, fo (stripReference w y S (u,t))) -
        (stripReference w y S (u,v)).2‖ ≤ (H+(L : ℝ)*(J : ℝ)+T*(L : ℝ)*(J : ℝ)+1)*δ) := by
  let G := stripReference w y S
  have hG : Continuous G := continuous_stripReference S hw hy.continuous
  have hdiff u v (hv : v ∈ Icc S (S+δ)) : ‖G (u,v)-w u‖ ≤ (J : ℝ)*δ := by
    rw [norm_stripReference_sub]
    have hy' := norm_sub_le_lipschitz hy v S
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hv.1)] at hy'
    exact hy'.trans (mul_le_mul_of_nonneg_left (by linarith [hv.2]) J.coe_nonneg)
  have hci : T*(L : ℝ)*J ≤ H+(L : ℝ)*(J : ℝ)+T*(L : ℝ)*(J : ℝ)+1 := by
    have := mul_nonneg L.coe_nonneg J.coe_nonneg
    linarith
  have hco : H+(L : ℝ)*J ≤ H+(L : ℝ)*(J : ℝ)+T*(L : ℝ)*(J : ℝ)+1 := by
    have := mul_nonneg (mul_nonneg hT L.coe_nonneg) J.coe_nonneg
    linarith
  constructor
  · intro u hu v hv
    have heq : y v + (∫ s in 0..u, fi (G (s,v))) - (G (u,v)).1 =
        ∫ s in 0..u, fi (G (s,v))-fi (w s) := by
      change y v + (∫ s in 0..u, fi (G (s,v))) - ((w u).1+(y v-y S)) = _
      rw [intervalIntegral.integral_sub (f := fun s => fi (G (s,v)))
        (g := fun s => fi (w s))
        (((hfi.continuous.comp hG).comp
          (show Continuous (fun s : ℝ => (s,v)) by fun_prop)).intervalIntegrable (μ := volume) 0 u)
        ((hfi.continuous.comp hw).intervalIntegrable (μ := volume) 0 u),hold u hu]
      abel
    rw [heq]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := u) (C := (L : ℝ)*J*δ)
      (f := fun s => fi (G (s,v))-fi (w s)) (fun s hs => by
        exact (norm_sub_le_lipschitz hfi _ _).trans
          ((mul_le_mul_of_nonneg_left (hdiff s v hv) L.coe_nonneg).trans_eq (by ring)))
    rw [sub_zero,abs_of_nonneg hu.1] at hi
    exact hi.trans (((mul_le_mul_of_nonneg_left (hu.2.trans hd.2)
      (mul_nonneg (mul_nonneg L.coe_nonneg J.coe_nonneg) hδ)).trans_eq (by ring)).trans
      (mul_le_mul_of_nonneg_right hci hδ))
  · intro u hu v hv
    change ‖(w u).2 + (∫ t in S..v, fo (G (u,t)))-(w u).2‖ ≤ _
    rw [add_sub_cancel_left]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := S) (b := v) (C := H+(L : ℝ)*J*δ) (f := fun t => fo (G (u,t)))
      (fun t ht => by
        rw [uIoc_of_le hv.1] at ht
        have ht' : t ∈ Icc S (S+δ) := ⟨ht.1.le,ht.2.trans hv.2⟩
        calc
          ‖fo (G (u,t))‖ = ‖(fo (G (u,t))-fo (w u))+fo (w u)‖ := by rw [sub_add_cancel]
          _ ≤ ‖fo (G (u,t))-fo (w u)‖+‖fo (w u)‖ := norm_add_le _ _
          _ ≤ (L : ℝ)*((J : ℝ)*δ)+H := add_le_add
            ((norm_sub_le_lipschitz hfo _ _).trans
              (mul_le_mul_of_nonneg_left (hdiff u t ht') L.coe_nonneg)) (hout u hu)
          _ = _ := by ring)
    rw [abs_of_nonneg (sub_nonneg.mpr hv.1)] at hi
    have hcoef : 0 ≤ H+(L : ℝ)*J*δ := by positivity
    have hcoef' : H+(L : ℝ)*J*δ ≤ H+(L : ℝ)*(J : ℝ) := by
      have := mul_le_mul_of_nonneg_left hδ₁ (mul_nonneg L.coe_nonneg J.coe_nonneg)
      linarith
    exact hi.trans ((mul_le_mul_of_nonneg_left (by linarith [hv.2]) hcoef).trans
      (mul_le_mul_of_nonneg_right (hcoef'.trans hco) hδ))

omit [CompleteSpace I] [CompleteSpace O] in
private theorem strip_lower_trace {L : ℝ≥0} {S d δ : ℝ}
    {fi : I × O → I} {fo : I × O → O} {w : ℝ → I × O} {y : ℝ → I}
    {F : ℝ × ℝ → I × O} (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hfi : LipschitzWith L fi) (hfo : LipschitzWith L fo) (hw : Continuous w)
    (hF : Continuous F)
    (hold : ∀ u ∈ Icc 0 d, (w u).1 = y S + ∫ s in 0..u, fi (w s))
    (hFi : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S + δ),
      (F (u, v)).1 = y v + ∫ s in 0..u, fi (F (s, v)))
    (hFo : ∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S + δ),
      (F (u, v)).2 = (w u).2 + ∫ t in S..v, fo (F (u, t))) :
    ∀ u ∈ Icc 0 d, F (u,S)=w u := by
  have hsmall : 2*(L : ℝ) ≤ 2*((L : ℝ)+1) := by linarith
  have hh := rectangle_goursat_distance_of_residual (F := F) (G := fun p => w p.1)
    (fi := fi) (fo := fo) (yi := y) (xb := fun u => (w u).2)
    (a := 0) (b := d) (c := S) (d := S) hd le_rfl L.coe_nonneg
    (by positivity : 0 < 2*((L : ℝ)+1)) hsmall le_rfl hF
    (hw.comp continuous_fst) hfi.continuous hfo.continuous
    (fun u hu v hv => hFi u hu v ⟨hv.1,by linarith [hv.2]⟩)
    (fun u hu v hv => hFo u hu v ⟨hv.1,by linarith [hv.2]⟩)
    (fun u hu v hv => by
      have hv' : v=S := le_antisymm hv.2 hv.1
      subst v
      rw [← hold u hu,sub_self,norm_zero])
    (fun u hu v hv => by
      have hv' : v=S := le_antisymm hv.2 hv.1
      subst v
      simp)
    (fun p hp => norm_sub_le_lipschitz hfi _ _)
    (fun p hp => norm_sub_le_lipschitz hfo _ _)
  intro u hu
  have h := hh (u,S) ⟨hu,le_rfl,le_rfl⟩
  simp only [mul_zero,zero_mul] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Uniform continuous characteristic strips near an old lower trace.
The positive height depends only on `L,J,H,T,r`, before the source maps,
apex, width and boundary functions are chosen. Incoming old-trace equations
and a lower outgoing source bound suffice; the result matches that trace
exactly and stays within ordinary norm distance `r` throughout the strip. -/
theorem continuous_rectangle_strip (L J : ℝ≥0) (H T r : ℝ)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hr : 0 < r) :
    ∃ δ₀ > 0, ∀ (fi : I × O → I) (fo : I × O → O),
      LipschitzWith L fi → LipschitzWith L fo →
      ∀ S d δ : ℝ, d ∈ Icc 0 T → 0 < δ → δ ≤ δ₀ →
      ∀ (w : ℝ → I × O) (y : ℝ → I), Continuous w → LipschitzWith J y →
      (∀ u ∈ Icc 0 d, (w u).1 = y S+∫ s in 0..u, fi (w s)) →
      (∀ u ∈ Icc 0 d, ‖fo (w u)‖ ≤ H) →
      ∃ F : ℝ × ℝ → I × O, Continuous F ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
          (F (u,v)).1 = y v+∫ s in 0..u, fi (F (s,v))) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ),
          (F (u,v)).2 = (w u).2+∫ t in S..v, fo (F (u,t))) ∧
        (∀ u ∈ Icc 0 d, F (u,S)=w u) ∧
        (∀ u ∈ Icc 0 d, ∀ v ∈ Icc S (S+δ), ‖F (u,v)-w u‖ ≤ r) := by
  let C : ℝ := H+(L : ℝ)*(J : ℝ)+T*(L : ℝ)*(J : ℝ)+1
  let k : ℝ := 2*((L : ℝ)+1)
  let M : ℝ := 2*C*Real.exp (k*(T+1))+(J : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ₀ := min 1 (r/(M+1))
  have hδ₀ : 0 < δ₀ := lt_min zero_lt_one (div_pos hr (by linarith))
  refine ⟨δ₀,hδ₀,?_⟩
  intro fi fo hfi hfo S d δ hd hδ hδsmall w y hw hy hold hout
  have hδ₁ : δ ≤ 1 := hδsmall.trans (min_le_left _ _)
  have hδr : (M+1)*δ ≤ r := by
    have hh := (le_div_iff₀ (by linarith : 0 < M+1)).mp
      (hδsmall.trans (min_le_right _ _))
    simpa only [mul_comm] using hh
  have hε : 0 ≤ C*δ := mul_nonneg hC.le hδ.le
  obtain ⟨hGi,hGo⟩ := strip_reference_residual_bounds hH hT hd hδ.le hδ₁ hfi hfo hw hy hold hout
  obtain ⟨F,hF,hFi,hFo,hnear⟩ := continuous_rectangle_goursat_near_reference
    hd.1 (by linarith : S ≤ S+δ) hε fi fo y (fun u => (w u).2)
    hfi hfo hy.continuous hw.snd (stripReference w y S)
    (continuous_stripReference S hw hy.continuous) hGi hGo
  refine ⟨F,hF,hFi,hFo,strip_lower_trace hd.1 hδ.le hfi hfo hw hF hold hFi hFo,?_⟩
  intro u hu v hv
  have hn := hnear (u,v) ⟨hu,hv⟩
  have hdiff : ‖stripReference w y S (u,v)-w u‖ ≤ (J : ℝ)*δ := by
    rw [norm_stripReference_sub]
    have hy' := norm_sub_le_lipschitz hy v S
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hv.1)] at hy'
    exact hy'.trans (mul_le_mul_of_nonneg_left (by linarith [hv.2]) J.coe_nonneg)
  have hcoord : u-0+(v-S) ≤ T+1 := by linarith [hu.2,hd.2,hv.2]
  have hexp : Real.exp (k*(u-0+(v-S))) ≤ Real.exp (k*(T+1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcoord hk.le)
  calc
    ‖F (u,v)-w u‖ = ‖(F (u,v)-stripReference w y S (u,v))+
        (stripReference w y S (u,v)-w u)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖F (u,v)-stripReference w y S (u,v)‖+‖stripReference w y S (u,v)-w u‖ :=
      norm_add_le _ _
    _ ≤ 2*(C*δ)*Real.exp (k*(u-0+(v-S)))+(J : ℝ)*δ := add_le_add hn hdiff
    _ ≤ 2*(C*δ)*Real.exp (k*(T+1))+(J : ℝ)*δ :=
      add_le_add (mul_le_mul_of_nonneg_left hexp
        (by positivity : 0 ≤ 2*(C*δ))) (le_refl ((J : ℝ)*δ))
    _ = M*δ := by dsimp [M]; ring
    _ ≤ (M+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ ≤ r := hδr

end EmcsfAcExtension.Local
