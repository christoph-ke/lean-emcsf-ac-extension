module

public import EmcsfAcExtension.Local.Calculus.MixedIdentity

/-! # Integral mixed derivatives on off-axis triangle sections

Each point is placed in a closed rectangle separated from the axis. The rectangle
calculus includes the initial and terminal triangle edges; locality then restores
the complete characteristic section interval in the conclusion.
-/

public section

open Set Filter
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Recover the incoming derivative of the outgoing domain partial on the full
triangle section. All source regularity is required only off the axis, and the
mixed derivative is recovered solely through the rectangle integral theorem. -/
theorem mixed_u_pdV_triangle_of_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f G Gv : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hG : ContinuousOn (Function.uncurry G) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (hGv : ContinuousOn (Function.uncurry Gv)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (heq : ∀ x y, 0 ≤ x → x < y → y ≤ T → pdU (triangle 0 T) f x y = G x y)
    (hd : ∀ x y, 0 ≤ x → x < y → y ≤ T →
      HasDerivWithinAt (G x) (Gv x y) (Icc x T) y)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => pdV (triangle 0 T) f x v) (Gv u v) (Icc 0 v) u := by
  let b := (2 * u + v) / 3
  let c := (u + 2 * v) / 3
  have hub : u < b := by dsimp [b]; linarith only [huv]
  have hbc : b < c := by dsimp [b, c]; linarith only [huv]
  have hcv : c < v := by dsimp [c]; linarith only [huv]
  have h0b : 0 < b := hu.trans_lt hub
  have hcT : c < T := hcv.trans_le hvT
  have hmem (x y : ℝ) (hx : x ∈ Icc 0 b) (hy : y ∈ Icc c T) :
      (x, y) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} :=
    ⟨hx.1, hx.2.trans_lt (hbc.trans_le hy.1), hy.2⟩
  have hs : Icc 0 b ×ˢ Icc c T ⊆ triangle 0 T :=
    fun p hp => ⟨hp.1.1, (hmem p.1 p.2 hp.1 hp.2).2.1.le, hp.2.2⟩
  have hm := mixed_u_pdV_of_transport_aux (f := f) (G := G) (Gv := Gv) h0b hcT hs hf
    (hG.comp (continuousOn_snd.prodMk continuousOn_fst)
      (fun p hp => hmem p.2 p.1 hp.2 hp.1))
    (hGv.comp (continuousOn_snd.prodMk continuousOn_fst)
      (fun p hp => hmem p.2 p.1 hp.2 hp.1))
    (fun x hx y hy => heq x y hx.1 (hmem x y hx hy).2.1 hy.2)
    (fun y hy x hx => (hd x y hx.1 (hmem x y hx hy).2.1 hy.2).mono
      (fun z hz => ⟨hx.2.trans (hbc.le.trans hz.1), hz.2⟩))
    ⟨hu, hub.le⟩ ⟨hcv.le, hvT⟩
  apply hm.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hub)] with x hx hxb
  exact ⟨hx.1, hxb.le⟩

/-- Recover the outgoing derivative of the incoming domain partial on the full
triangle section, using the other orientation of the same closed rectangle
integral representation. No C² premise is introduced. -/
theorem mixed_v_pdU_triangle_of_transport_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f G Gu : ℝ → ℝ → E}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    (hG : ContinuousOn (Function.uncurry G) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (hGu : ContinuousOn (Function.uncurry Gu)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T})
    (heq : ∀ x y, 0 ≤ x → x < y → y ≤ T → pdV (triangle 0 T) f x y = G x y)
    (hd : ∀ x y, 0 ≤ x → x < y → y ≤ T →
      HasDerivWithinAt (fun z => G z y) (Gu x y) (Icc 0 y) x)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun y => pdU (triangle 0 T) f u y) (Gu u v) (Icc u T) v := by
  let b := (2 * u + v) / 3
  let c := (u + 2 * v) / 3
  have hub : u < b := by dsimp [b]; linarith only [huv]
  have hbc : b < c := by dsimp [b, c]; linarith only [huv]
  have hcv : c < v := by dsimp [c]; linarith only [huv]
  have h0b : 0 < b := hu.trans_lt hub
  have hcT : c < T := hcv.trans_le hvT
  have hmem (x y : ℝ) (hx : x ∈ Icc 0 b) (hy : y ∈ Icc c T) :
      (x, y) ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T} :=
    ⟨hx.1, hx.2.trans_lt (hbc.trans_le hy.1), hy.2⟩
  have hs : Icc 0 b ×ˢ Icc c T ⊆ triangle 0 T :=
    fun p hp => ⟨hp.1.1, (hmem p.1 p.2 hp.1 hp.2).2.1.le, hp.2.2⟩
  have hm := mixed_v_pdU_of_transport_aux (f := f) (G := G) (Gu := Gu) h0b hcT hs hf
    (hG.mono (fun p hp => hmem p.1 p.2 hp.1 hp.2))
    (hGu.mono (fun p hp => hmem p.1 p.2 hp.1 hp.2))
    (fun x hx y hy => heq x y hx.1 (hmem x y hx hy).2.1 hy.2)
    (fun x hx y hy => (hd x y hx.1 (hmem x y hx hy).2.1 hy.2).mono
      (fun z hz => ⟨hz.1, hz.2.trans (hbc.le.trans hy.1)⟩))
    ⟨hu, hub.le⟩ ⟨hcv.le, hvT⟩
  apply hm.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcv)] with y hy hcy
  exact ⟨hcy.le, hy.2⟩

end EmcsfAcExtension.Local
