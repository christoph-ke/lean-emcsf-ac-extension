module

public import Mathlib
public import EmcsfAcExtension.Frozen.Fields

/-! # Root A Relabel

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
Selected-cone coordinate label, charged_SF_new_version.tex:L3954–L4161. -/
noncomputable def selectedRelabel (S : Fields) (us t : ℝ) : ℝ := 2 * S.r us t

/-- [internal]
Constant datum prolongation, charged_SF_new_version.tex:L4162–L4184 and L6593–L6604. -/
def extendDatum (h : ℝ → ℂ) (L t : ℝ) : ℂ := h (min t L)

/-- [internal]
Null-coordinate pullback of all nine fields, charged_SF_new_version.tex:L3954–L4161 and L4189–L4193.
-/
noncomputable def nullPullback (S : Fields) (U V : ℝ → ℝ) : Fields where
  r u v := S.r (U u) (V v)
  lam u v := deriv V v * S.lam (U u) (V v)
  nu u v := deriv U u * S.nu (U u) (V v)
  m u v := S.m (U u) (V v)
  Q u v := S.Q (U u) (V v)
  phi u v := S.phi (U u) (V v)
  A u v := deriv U u * S.A (U u) (V v)
  theta u v := deriv V v * S.theta (U u) (V v)
  xi u v := deriv U u * S.xi (U u) (V v)

/-- [internal]
Length rescaling with coupling transformed to a*e, charged_SF_new_version.tex:L1964–L1988. -/
noncomputable def rescaleFields (S : Fields) (a : ℝ) : Fields where
  r u v := S.r (a * u) (a * v) / a
  lam u v := S.lam (a * u) (a * v)
  nu u v := S.nu (a * u) (a * v)
  m u v := S.m (a * u) (a * v) / a
  Q u v := S.Q (a * u) (a * v) / a
  phi u v := S.phi (a * u) (a * v)
  A u v := S.A (a * u) (a * v)
  theta u v := S.theta (a * u) (a * v)
  xi u v := S.xi (a * u) (a * v)

/-- [internal]
Residual incoming gauge transformation, charged_SF_new_version.tex:L692–L699 and L1957–L1963. -/
noncomputable def gaugeFields (e : ℝ) (S : Fields) (χ : ℝ → ℝ) : Fields where
  r := S.r
  lam := S.lam
  nu := S.nu
  m := S.m
  Q := S.Q
  phi u v := Complex.exp (I * e * χ u) * S.phi u v
  A u v := S.A u v - deriv χ u
  theta u v := Complex.exp (I * e * χ u) * S.theta u v
  xi u v := Complex.exp (I * e * χ u) * S.xi u v

/-- [internal]
Increasing C¹ label with positive locally BV derivative,
charged_SF_new_version.tex:L4137–L4161 and L4189–L4193. -/
def IsNullRelabel (F : ℝ ≃o ℝ) : Prop :=
  ContDiff ℝ 1 (F : ℝ → ℝ) ∧ (∀ t, 0 < deriv (F : ℝ → ℝ) t) ∧
    ∀ a b, eVariationOn (deriv (F : ℝ → ℝ)) (Icc a b) < ⊤

end EmcsfAcExtension.Global
