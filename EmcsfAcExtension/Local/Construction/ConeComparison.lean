module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Broad.GeometryCone

/-! # Agreement of C¹ reconstructed entering blocks

These primitive arguments work on a complete outgoing cone inside a
wedge or the nonconvex old-triangle/strip union. They require no broad
solution on that larger domain and prescribe no future axis value.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The zero-axis radius is the expansion primitive on any contained
complete outgoing cone of a C¹ solution. -/
theorem c1_radius_primitive_on_cone {e c b : ℝ} {F : Fields} {D : Set (ℝ × ℝ)}
    (hF : IsC1Solution e F D) (hcb : c ≤ b) (hs : outSeg c c b ⊆ D) :
    F.r c b = ∫ v in c..b, F.lam c v := by
  have hr := continuousOn_out_section hF.c1_r.continuousOn hs
  have hl := continuousOn_out_section hF.c1_lam.continuousOn hs
  have hi := hl.intervalIntegrable_of_Icc (μ := volume) hcb
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcb hr
    (f' := F.lam c) (fun v hv => ?_) hi
  · simpa only [(hF.axis c (hs ⟨rfl, le_rfl, hcb⟩)).1, sub_zero] using he.symm
  · have hd := (hasDerivWithinAt_pdV hF.c1_r (hs ⟨rfl, hv.1.le, hv.2.le⟩)
      (fun v hv => hs ⟨rfl, hv⟩)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    rwa [(hF.eq_v (c,v) (hs ⟨rfl, hv.1.le, hv.2.le⟩) hv.1).1] at hd

end EmcsfAcExtension.Local
