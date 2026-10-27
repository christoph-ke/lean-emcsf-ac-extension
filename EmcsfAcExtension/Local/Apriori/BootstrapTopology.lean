module

public import Mathlib
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Infra.Null.Parametric
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseContinuity

/-! # A continuous barrier on growing complete triangles

A fixed compact reference triangle parametrizes every positive apex. Its
maximum varies continuously, so strict improvement prevents first failure.
The vertex is treated directly and no derivative on a degenerate triangle
is used (internal project record (30), definitions-audit note N3).
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- A continuous real barrier on a complete triangle remains negative when
it starts negative at the vertex and every nonpositive complete subtriangle
has strict improvement. This qualitative continuity bootstrap is uniform in
all functions and time scales, with no estimate constant. -/
theorem complete_triangle_barrier {T : ℝ} {F : ℝ × ℝ → ℝ} (hT : 0 < T)
    (cF : ContinuousOn F (triangle 0 T)) (hF0 : F (0, 0) < 0)
    (hstep : ∀ s ∈ Icc 0 T, (∀ p ∈ triangle 0 s, F p ≤ 0) →
      ∀ p ∈ triangle 0 s, F p < 0) : ∀ p ∈ triangle 0 T, F p < 0 := by
  let U := triangle (0 : ℝ) 1
  let G := fun p : ℝ × ℝ => F (triangleProj 0 T p)
  have cG : Continuous G := continuous_comp_triangleProj
    (F := fun x y : ℝ => F (x, y)) hT.le (by simpa only [Function.uncurry_def] using cF)
  let Z := fun s : ℝ => sSup ((fun p : ℝ × ℝ => G (s * p.1, s * p.2)) '' U)
  have cZ : Continuous Z := (isCompact_triangle (0 : ℝ) 1).continuous_sSup
    (f := fun (s : ℝ) (p : ℝ × ℝ) => G (s * p.1, s * p.2))
    (cG.comp (show Continuous (fun z : ℝ × (ℝ × ℝ) =>
      (z.1 * z.2.1, z.1 * z.2.2)) by fun_prop))
  have hG (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) : G p = F p := by
    dsimp only [G]
    rw [triangleProj_of_mem hp]
  have himage (s : ℝ) (hs : s ∈ Icc 0 T) :
      (fun p : ℝ × ℝ => G (s * p.1, s * p.2)) '' U = F '' triangle 0 s := by
    apply Subset.antisymm
    · rintro y ⟨p, hp, rfl⟩
      have hsp : (s * p.1, s * p.2) ∈ triangle 0 s :=
        ⟨mul_nonneg hs.1 hp.1, mul_le_mul_of_nonneg_left hp.2.1 hs.1,
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2.2 hs.1⟩
      refine ⟨(s * p.1, s * p.2), hsp, ?_⟩
      exact (hG _ ⟨hsp.1, hsp.2.1, hsp.2.2.trans hs.2⟩).symm
    · rintro y ⟨⟨a, b⟩, hp, rfl⟩
      rcases eq_or_lt_of_le hs.1 with hs0 | hs0
      · change 0 = s at hs0
        subst s
        have hb : b = 0 := by linarith only [hp.1, hp.2.1, hp.2.2]
        have ha : a = 0 := by linarith only [hp.1, hp.2.1, hb]
        subst a
        subst b
        refine ⟨(0, 0), ⟨le_rfl, le_rfl, by norm_num⟩, ?_⟩
        simp only [zero_mul]
        exact hG (0, 0) ⟨le_rfl, le_rfl, hT.le⟩
      · have hp' : (a / s, b / s) ∈ U :=
          ⟨div_nonneg hp.1 hs0.le, div_le_div_of_nonneg_right hp.2.1 hs0.le,
            (div_le_one hs0).mpr hp.2.2⟩
        refine ⟨(a / s, b / s), hp', ?_⟩
        have ha : s * (a / s) = a := by field_simp
        have hb : s * (b / s) = b := by field_simp
        dsimp only
        rw [ha, hb]
        exact hG (a, b) ⟨hp.1, hp.2.1, hp.2.2.trans hs.2⟩
  have hZ (s : ℝ) (hs : s ∈ Icc 0 T) : Z s = sSup (F '' triangle 0 s) := by
    dsimp only [Z]
    rw [himage s hs]
  have hZ0 : Z 0 = F (0, 0) := by
    dsimp only [Z]
    have himg : (fun p : ℝ × ℝ => G (0 * p.1, 0 * p.2)) '' U = {F (0, 0)} := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        simp only [zero_mul, mem_singleton_iff]
        exact hG (0, 0) ⟨le_rfl, le_rfl, hT.le⟩
      · intro hy
        rw [mem_singleton_iff] at hy
        subst y
        refine ⟨(0, 0), ⟨le_rfl, le_rfl, by norm_num⟩, ?_⟩
        simp only [zero_mul]
        exact hG (0, 0) ⟨le_rfl, le_rfl, hT.le⟩
    rw [himg, csSup_singleton]
  have hZstep (s : ℝ) (hs : s ∈ Icc 0 T) (hz : Z s ≤ 0) : Z s < 0 := by
    have hsub : triangle 0 s ⊆ triangle 0 T := fun p hp =>
      ⟨hp.1, hp.2.1, hp.2.2.trans hs.2⟩
    have cs := cF.mono hsub
    have hb := (isCompact_triangle (0 : ℝ) s).bddAbove_image cs
    have hclosed (p : ℝ × ℝ) (hp : p ∈ triangle 0 s) : F p ≤ 0 := by
      apply (le_csSup hb (mem_image_of_mem F hp)).trans
      rwa [hZ s hs] at hz
    have hstrict := hstep s hs hclosed
    obtain ⟨p, hp, hmax⟩ := (isCompact_triangle (0 : ℝ) s).exists_isMaxOn
      ⟨(0, 0), le_rfl, le_rfl, hs.1⟩ cs
    rw [hZ s hs]
    apply (csSup_le ((show (triangle 0 s).Nonempty from
      ⟨(0, 0), le_rfl, le_rfl, hs.1⟩).image F) ?_).trans_lt (hstrict p hp)
    rintro y ⟨q, hq, rfl⟩
    exact hmax hq
  have hz0 : Z 0 < 0 := by rw [hZ0]; exact hF0
  have hall := coupled_bounds_of_strict_improvement cZ.continuousOn
    (continuousOn_const (c := (-1 : ℝ))) hz0 (by norm_num : (-1 : ℝ) < 0)
    (fun s hs hz _ => ⟨hZstep s hs hz, by norm_num⟩)
  intro p hp
  have hZfinal := (hall T ⟨hT.le, le_rfl⟩).1
  rw [hZ T ⟨hT.le, le_rfl⟩] at hZfinal
  exact (le_csSup ((isCompact_triangle (0 : ℝ) T).bddAbove_image cF)
    (mem_image_of_mem F hp)).trans_lt hZfinal

end EmcsfAcExtension.Local
