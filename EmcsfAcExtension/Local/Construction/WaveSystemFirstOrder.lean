module

public import EmcsfAcExtension.Local.Construction.WaveSystem
public import EmcsfAcExtension.Local.Construction.FullSystemMixed

/-! # C¹ first-order wave recovery from the actual rφ primitive

The mixed derivative used here is the derivative of the incoming partial
of the outgoing primitive. The two curve lemmas record the product-rule
computations used in internal project record (23)–(25), without a C² field premise.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- Recover the incoming scalar transport from the covariant rφ wave
identity and first derivatives. `X` is the value of `r D_u φ` at the point;
no derivative of `X` is assumed. -/
theorem hasDerivWithinAt_theta_of_wave_primitive {s : Set ℝ} {u : ℝ}
    {L : ℝ → ℝ} {N P : ℝ → ℂ} (r nu mu q e A : ℝ) (theta X : ℂ)
    (hr : r ≠ 0) (hd : 1 - mu ≠ 0)
    (hN : N u = (L u : ℂ) * P u + theta)
    (dN : HasDerivWithinAt N
      ((nu : ℂ) * L u / ((1 - (mu : ℂ)) * (r : ℂ) ^ 2) *
          ((mu : ℂ) - (q : ℂ) ^ 2 / (r : ℂ) ^ 2 - I * e * q) * ((r : ℂ) * P u) -
        I * e * A * N u) s u)
    (dL : HasDerivWithinAt L (nu * L u / r * ((mu - q ^ 2 / r ^ 2) / (1 - mu))) s u)
    (dP : HasDerivWithinAt P (X / (r : ℂ) - I * e * A * P u) s u) :
    HasDerivWithinAt (fun x => N x - (L x : ℂ) * P x)
      (-(I * e * A * theta) - (L u : ℂ) * X / (r : ℂ) -
        I * e * q * P u * nu * L u / ((1 - (mu : ℂ)) * r)) s u := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hdC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hd
  convert dN.sub (dL.ofReal_comp.mul dP) using 1
  rw [hN]
  push_cast
  field_simp [hrC, hdC]
  ring

/-- Differentiate the actual representation
`X = (rφ)_u - νφ + ie A (rφ)` in the outgoing direction. The incoming
partial has its derivative from the outgoing primitive's C¹ source;
all other derivatives are first derivatives of primary fields. -/
theorem hasDerivAt_xi_of_wave_primitive {v : ℝ} {W N P : ℝ → ℂ} {V A : ℝ → ℝ}
    (r lam mu q e : ℝ) (theta J : ℂ) (hr : r ≠ 0) (hd : 1 - mu ≠ 0)
    (hN : N v = (r : ℂ) * P v) (hJ : J = (lam : ℂ) * P v + theta)
    (dW : HasDerivAt W
      ((V v : ℂ) * lam / ((1 - (mu : ℂ)) * (r : ℂ) ^ 2) *
          ((mu : ℂ) - (q : ℂ) ^ 2 / (r : ℂ) ^ 2 - I * e * q) * N v -
        I * e * A v * J) v)
    (dN : HasDerivAt N J v)
    (dV : HasDerivAt V (V v * lam / r * ((mu - q ^ 2 / r ^ 2) / (1 - mu))) v)
    (dP : HasDerivAt P (theta / (r : ℂ)) v)
    (dA : HasDerivAt A (2 * V v * lam * q / ((1 - mu) * r ^ 2)) v) :
    HasDerivAt (fun x => W x - (V x : ℂ) * P x + I * e * A x * N x)
      (-((V v : ℂ) * theta / r) +
        I * e * q * P v * V v * lam / ((1 - (mu : ℂ)) * r)) v := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hdC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hd
  have hc := ((dA.ofReal_comp.const_mul (I * e)).mul dN)
  convert (dW.sub (dV.ofReal_comp.mul dP)).add hc using 1
  rw [hN, hJ]
  push_cast
  field_simp [hrC, hdC]
  ring

end EmcsfAcExtension.Local.Null
