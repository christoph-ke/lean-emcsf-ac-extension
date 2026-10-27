module

public import Mathlib

/-! # Algebraic cores of the Raychaudhuri identities

The quotient and logarithm differentiation is left to the calculus layer. These lemmas
substitute the reduced radius and mass equations, with `μ = 2m/r`, into their resulting
rational expressions (`charged_SF_new_version.tex:L4336`).
-/

public section

namespace EmcsfAcExtension.Local

/-- [node restart-eq-ray]
Incoming Raychaudhuri identity after differentiating `log(λ/(1-μ))`.
The four nonvanishing assumptions are exactly its denominators. -/
theorem eq_ray_in_algebra {r lam nu m Q lamU mU : ℝ} {xi : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - 2 * m / r ≠ 0)
    (hlamU : lamU = nu * lam / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hmU : mU = (1 - 2 * m / r) * ‖xi‖ ^ 2 / (2 * nu) + Q ^ 2 * nu / (2 * r ^ 2)) :
    lamU / lam + (2 * mU / r - 2 * m * nu / r ^ 2) / (1 - 2 * m / r) =
      ‖xi‖ ^ 2 / (nu * r) := by
  rw [hlamU, hmU]
  have hden : r - 2 * m ≠ 0 := by
    intro h
    apply hmu
    field_simp [hr]
    linear_combination h
  field_simp [hr, hlam, hnu, hden]
  ring

/-- [node restart-eq-ray]
Outgoing Raychaudhuri identity after differentiating `log(-ν/(1-μ))`.
The four nonvanishing assumptions are exactly its denominators. -/
theorem eq_ray_out_algebra {r lam nu m Q nuV mV : ℝ} {theta : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - 2 * m / r ≠ 0)
    (hnuV : nuV = nu * lam / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hmV : mV = (1 - 2 * m / r) * ‖theta‖ ^ 2 / (2 * lam) + Q ^ 2 * lam / (2 * r ^ 2)) :
    nuV / nu + (2 * mV / r - 2 * m * lam / r ^ 2) / (1 - 2 * m / r) =
      ‖theta‖ ^ 2 / (lam * r) := by
  rw [hnuV, hmV]
  have hden : r - 2 * m ≠ 0 := by
    intro h
    apply hmu
    field_simp [hr]
    linear_combination h
  field_simp [hr, hlam, hnu, hden]
  ring

end EmcsfAcExtension.Local
