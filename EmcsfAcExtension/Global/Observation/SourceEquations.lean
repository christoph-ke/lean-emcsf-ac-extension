module

public import EmcsfAcExtension.Global.Observation.DomainBridge
public import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Ordinary characteristic equations strictly inside the source domain

The enclosing characteristic sections have strict margins around every
comparison point. Continuous frozen equation sources and the supplied
internal project record FTC then give ordinary derivatives at that point, including
endpoints of a smaller comparison section.
Source: charged_SF_new_version.tex:L2782–2783; approved internal project record AC justification.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
All thirteen ordinary characteristic derivatives at an interior,
positive-radius point follow from the original frozen integral equations.
The strict source-label margins are explicit; there is no upgrade of a
within derivative at an original-domain endpoint. No constants occur. -/
theorem original_characteristic_equations {e ui u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hi : ui < u) (huv : u < v) (hv : v < 0) :
    (HasDerivAt (S.r u) (S.lam u v) v ∧
      HasDerivAt (S.nu u) (S.rUV u v) v ∧
      HasDerivAt (S.m u) (S.mV u v) v ∧
      HasDerivAt (S.Q u) (S.QV e u v) v ∧
      HasDerivAt (S.A u) (S.AV u v) v ∧
      HasDerivAt (S.phi u) (S.phiV u v) v ∧
      HasDerivAt (S.xi u) (S.xiV e u v) v) ∧
    (HasDerivAt (fun x => S.r x v) (S.nu u v) u ∧
      HasDerivAt (fun x => S.lam x v) (S.rUV u v) u ∧
      HasDerivAt (fun x => S.m x v) (S.mU u v) u ∧
      HasDerivAt (fun x => S.Q x v) (S.QU e u v) u ∧
      HasDerivAt (fun x => S.phi x v) (S.phiU e u v) u ∧
      HasDerivAt (fun x => S.theta x v) (S.thetaU e u v) u) := by
  have houtmem (x) (hx : x ∈ Ioo u 0) : (u, x) ∈ origDomain ui :=
    ⟨hi.le, huv.trans hv, hx.1.le, hx.2.le⟩
  have hinmem (x) (hx : x ∈ Ioo ui v) : (x, v) ∈ origDomain ui :=
    ⟨hx.1.le, hx.2.trans hv, hx.2.le, hv.le⟩
  have out {E : Type} [TopologicalSpace E] {F : ℝ → ℝ → E}
      (hF : ContinuousOn (Function.uncurry F) (origDomain ui)) :
      ContinuousOn (F u) (Ioo u 0) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn houtmem
  have inn {E : Type} [TopologicalSpace E] {F : ℝ → ℝ → E}
      (hF : ContinuousOn (Function.uncurry F) (origDomain ui)) :
      ContinuousOn (fun x => F x v) (Ioo ui v) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn hinmem
  have ro (x) (hx : x ∈ Ioo u 0) : S.r u x ≠ 0 :=
    (hS.r_pos (u, x) (houtmem x hx) hx.1).ne'
  have ri (x) (hx : x ∈ Ioo ui v) : S.r x v ≠ 0 :=
    (hS.r_pos (x, v) (hinmem x hx) hx.2).ne'
  have go (x) (hx : x ∈ Ioo u 0) : 1 - S.mu u x ≠ 0 :=
    (hS.one_sub_mu_pos _ (houtmem x hx)).ne'
  have gi (x) (hx : x ∈ Ioo ui v) : 1 - S.mu x v ≠ 0 :=
    (hS.one_sub_mu_pos _ (hinmem x hx)).ne'
  have lo (x) (hx : x ∈ Ioo u 0) : S.lam u x ≠ 0 :=
    (hS.lam_pos _ (houtmem x hx)).ne'
  have ni (x) (hx : x ∈ Ioo ui v) : S.nu x v ≠ 0 :=
    (hS.nu_neg _ (hinmem x hx)).ne
  have cro := out hS.cont_r
  have clo := out hS.cont_lam
  have cno := out hS.cont_nu
  have cmo := out hS.cont_m
  have cqo := out hS.cont_Q
  have cao := out hS.cont_A
  have cpo := out hS.cont_phi
  have cto := out hS.cont_theta
  have cxo := out hS.cont_xi
  have cri := inn hS.cont_r
  have cli := inn hS.cont_lam
  have cni := inn hS.cont_nu
  have cmi := inn hS.cont_m
  have cqi := inn hS.cont_Q
  have cai := inn hS.cont_A
  have cpi := inn hS.cont_phi
  have cti := inn hS.cont_theta
  have cxi := inn hS.cont_xi
  have lifto {f : ℝ → ℝ} (cf : ContinuousOn f (Ioo u 0)) :
      ContinuousOn (fun x => (f x : ℂ)) (Ioo u 0) :=
    Complex.continuous_ofReal.comp_continuousOn cf
  have cmuo : ContinuousOn (S.mu u) (Ioo u 0) := by
    simpa only [Fields.mu] using! (continuousOn_const.mul cmo).div cro ro
  have cruvo : ContinuousOn (S.rUV u) (Ioo u 0) := by
    simpa only [Fields.rUV] using!
      ((cno.mul clo).div cro ro).mul
        ((cmuo.sub ((cqo.pow 2).div (cro.pow 2)
          (fun x hx => pow_ne_zero 2 (ro x hx)))).div (continuousOn_const.sub cmuo) go)
  have cmvo : ContinuousOn (S.mV u) (Ioo u 0) := by
    simpa only [Fields.mV] using!
      (((continuousOn_const.sub cmuo).mul (cto.norm.pow 2)).div
        (continuousOn_const.mul clo) (fun x hx => mul_ne_zero (by norm_num) (lo x hx))).add
      (((cqo.pow 2).mul clo).div (continuousOn_const.mul (cro.pow 2))
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 2 (ro x hx))))
  have cqvo : ContinuousOn (S.QV e u) (Ioo u 0) := by
    simpa only [Fields.QV] using!
      ((continuousOn_const.mul cro).mul (continuous_im.comp_continuousOn (cpo.star.mul cto))).neg
  have cavo : ContinuousOn (S.AV u) (Ioo u 0) := by
    simpa only [Fields.AV] using!
      (((continuousOn_const.mul cno).mul clo).mul cqo).div
        ((continuousOn_const.sub cmuo).mul (cro.pow 2))
        (fun x hx => mul_ne_zero (go x hx) (pow_ne_zero 2 (ro x hx)))
  have cpvo : ContinuousOn (S.phiV u) (Ioo u 0) := by
    simpa only [Fields.phiV] using!
      cto.div (lifto cro) (fun x hx => Complex.ofReal_ne_zero.mpr (ro x hx))
  have cwvo : ContinuousOn (S.waveSource e u) (Ioo u 0) := by
    simpa only [Fields.waveSource, Pi.mul_apply, Pi.sub_apply, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one] using!
      (((((continuousOn_const (c := I * (e : ℂ))).mul (lifto cqo)).mul cpo).mul (lifto cno)).mul
        (lifto clo)).div (lifto ((continuousOn_const.sub cmuo).mul cro))
        (fun x hx => Complex.ofReal_ne_zero.mpr (mul_ne_zero (go x hx) (ro x hx)))
  have cxvo : ContinuousOn (S.xiV e u) (Ioo u 0) := by
    simpa only [Fields.xiV] using!
      (((lifto cno).mul cto).div (lifto cro)
        (fun x hx => Complex.ofReal_ne_zero.mpr (ro x hx))).neg.add cwvo
  have lifti {f : ℝ → ℝ} (cf : ContinuousOn f (Ioo ui v)) :
      ContinuousOn (fun x => (f x : ℂ)) (Ioo ui v) :=
    Complex.continuous_ofReal.comp_continuousOn cf
  have cmui : ContinuousOn (fun x => S.mu x v) (Ioo ui v) := by
    simpa only [Fields.mu] using! (continuousOn_const.mul cmi).div cri ri
  have cruvi : ContinuousOn (fun x => S.rUV x v) (Ioo ui v) := by
    simpa only [Fields.rUV] using!
      ((cni.mul cli).div cri ri).mul
        ((cmui.sub ((cqi.pow 2).div (cri.pow 2)
          (fun x hx => pow_ne_zero 2 (ri x hx)))).div (continuousOn_const.sub cmui) gi)
  have cmui' : ContinuousOn (fun x => S.mU x v) (Ioo ui v) := by
    simpa only [Fields.mU] using!
      (((continuousOn_const.sub cmui).mul (cxi.norm.pow 2)).div
        (continuousOn_const.mul cni) (fun x hx => mul_ne_zero (by norm_num) (ni x hx))).add
      (((cqi.pow 2).mul cni).div (continuousOn_const.mul (cri.pow 2))
        (fun x hx => mul_ne_zero (by norm_num) (pow_ne_zero 2 (ri x hx))))
  have cqui : ContinuousOn (fun x => S.QU e x v) (Ioo ui v) := by
    simpa only [Fields.QU] using!
      (continuousOn_const.mul cri).mul (continuous_im.comp_continuousOn (cpi.star.mul cxi))
  have cpui : ContinuousOn (fun x => S.phiU e x v) (Ioo ui v) := by
    simpa only [Fields.phiU] using!
      (cxi.div (lifti cri) (fun x hx => Complex.ofReal_ne_zero.mpr (ri x hx))).sub
        ((continuousOn_const.mul (lifti cai)).mul cpi)
  have cwui : ContinuousOn (fun x => S.waveSource e x v) (Ioo ui v) := by
    simpa only [Fields.waveSource, Pi.mul_apply, Pi.sub_apply, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one] using!
      (((((continuousOn_const (c := I * (e : ℂ))).mul (lifti cqi)).mul cpi).mul (lifti cni)).mul
        (lifti cli)).div (lifti ((continuousOn_const.sub cmui).mul cri))
        (fun x hx => Complex.ofReal_ne_zero.mpr (mul_ne_zero (gi x hx) (ri x hx)))
  have ctui : ContinuousOn (fun x => S.thetaU e x v) (Ioo ui v) := by
    simpa only [Fields.thetaU] using!
      (((continuousOn_const.mul (lifti cai)).mul cti).neg.sub
        (((lifti cli).mul cxi).div (lifti cri)
          (fun x hx => Complex.ofReal_ne_zero.mpr (ri x hx)))).sub cwui
  have hout (c d : ℝ) (hc : u < c) (hcd : c ≤ d) (hd : d < 0) :=
    hS.eq_out u c d hc hcd (show outSeg u c d ⊆ origDomain ui by
      rintro ⟨x, y⟩ ⟨rfl, hyc, hyd⟩
      exact ⟨hi.le, huv.trans hv, hc.le.trans hyc, hyd.trans hd.le⟩)
  have hin (c d : ℝ) (hc : ui < c) (hcd : c ≤ d) (hd : d < v) :=
    hS.eq_in c d v hcd hd (show inSeg c d v ⊆ origDomain ui by
      rintro ⟨x, y⟩ ⟨hcx, hxd, rfl⟩
      exact ⟨hc.le.trans hcx, (hxd.trans hd.le).trans_lt hv, hxd.trans hd.le, hv.le⟩)
  have dout {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F G : ℝ → E} (cG : ContinuousOn G (Ioo u 0))
      (heq : ∀ c d, u < c → c ≤ d → d < 0 → IntegralForm F G c d) :
      HasDerivAt F (G v) v :=
    ordinary_on_closed_of_margin huv hv cG heq v ⟨le_rfl, le_rfl⟩
  have din {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      {F G : ℝ → E} (cG : ContinuousOn G (Ioo ui v))
      (heq : ∀ c d, ui < c → c ≤ d → d < v → IntegralForm F G c d) :
      HasDerivAt F (G u) u :=
    ordinary_on_closed_of_margin hi huv cG heq u ⟨le_rfl, le_rfl⟩
  exact ⟨⟨dout clo (fun c d hc hcd hd => (hout c d hc hcd hd).1),
    dout cruvo (fun c d hc hcd hd => (hout c d hc hcd hd).2.1),
    dout cmvo (fun c d hc hcd hd => (hout c d hc hcd hd).2.2.1),
    dout cqvo (fun c d hc hcd hd => (hout c d hc hcd hd).2.2.2.1),
    dout cavo (fun c d hc hcd hd => (hout c d hc hcd hd).2.2.2.2.1),
    dout cpvo (fun c d hc hcd hd => (hout c d hc hcd hd).2.2.2.2.2.1),
    dout cxvo (fun c d hc hcd hd => (hout c d hc hcd hd).2.2.2.2.2.2)⟩,
    ⟨din cni (fun c d hc hcd hd => (hin c d hc hcd hd).1),
    din cruvi (fun c d hc hcd hd => (hin c d hc hcd hd).2.1),
    din cmui' (fun c d hc hcd hd => (hin c d hc hcd hd).2.2.1),
    din cqui (fun c d hc hcd hd => (hin c d hc hcd hd).2.2.2.1),
    din cpui (fun c d hc hcd hd => (hin c d hc hcd hd).2.2.2.2.1),
    din ctui (fun c d hc hcd hd => (hin c d hc hcd hd).2.2.2.2.2)⟩⟩

end EmcsfAcExtension.Global.Observation
