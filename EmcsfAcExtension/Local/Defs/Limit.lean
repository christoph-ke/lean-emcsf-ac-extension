module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Local.Defs.Renormalized

/-! # Strong limits of classical configurations

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Strong fixed-label convergence of `C¹` configurations `Sn` to a configuration `S` on `𝒟_T`
(charged_SF_new_version.tex:L5534–5560, charged_SF_new_version.tex:L6391–6459): uniform convergence
of the nine fields,
  and convergence of the
renormalized derivatives in the envelope (L¹_v L^∞_u) sense against the frozen `jOut`, `kIn`. -/
structure StrongLimit (e T : ℝ) (Sn : ℕ → Fields) (S : Fields) : Prop where
  /-- The `unif_r` clause of `StrongLimit` in internal project record. -/
  unif_r : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).r) (Function.uncurry S.r) atTop
    (triangle 0 T)
  /-- The `unif_lam` clause of `StrongLimit` in internal project record. -/
  unif_lam : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).lam) (Function.uncurry S.lam)
    atTop (triangle 0 T)
  /-- The `unif_nu` clause of `StrongLimit` in internal project record. -/
  unif_nu : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).nu) (Function.uncurry S.nu)
    atTop (triangle 0 T)
  /-- The `unif_m` clause of `StrongLimit` in internal project record. -/
  unif_m : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).m) (Function.uncurry S.m) atTop
    (triangle 0 T)
  /-- The `unif_Q` clause of `StrongLimit` in internal project record. -/
  unif_Q : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Q) (Function.uncurry S.Q) atTop
    (triangle 0 T)
  /-- The `unif_phi` clause of `StrongLimit` in internal project record. -/
  unif_phi : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi) (Function.uncurry S.phi)
    atTop (triangle 0 T)
  /-- The `unif_A` clause of `StrongLimit` in internal project record. -/
  unif_A : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).A) (Function.uncurry S.A) atTop
    (triangle 0 T)
  /-- The `unif_theta` clause of `StrongLimit` in internal project record. -/
  unif_theta : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).theta)
    (Function.uncurry S.theta) atTop (triangle 0 T)
  /-- The `unif_xi` clause of `StrongLimit` in internal project record. -/
  unif_xi : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).xi) (Function.uncurry S.xi)
    atTop (triangle 0 T)
  /-- The `env_j` clause of `StrongLimit` in internal project record. -/
  env_j : ∃ D : ℕ → ℝ → ℝ≥0∞, (∀ n, Measurable (D n)) ∧
    Tendsto (fun n => ∫⁻ v in Icc 0 T, D n v) atTop (𝓝 0) ∧
    ∀ n, ∀ u ∈ Icc 0 T, ∀ᵐ v ∂(volume.restrict (Icc u T)),
      ‖jC1 (triangle 0 T) (Sn n) u v - jOut S u v‖ₑ ≤ D n v
  /-- The `env_k` clause of `StrongLimit` in internal project record. -/
  env_k : ∃ D : ℕ → ℝ → ℝ≥0∞, (∀ n, Measurable (D n)) ∧
    Tendsto (fun n => ∫⁻ u in Icc 0 T, D n u) atTop (𝓝 0) ∧
    ∀ n, ∀ v ∈ Icc 0 T, ∀ᵐ u ∂(volume.restrict (Icc 0 v)),
      ‖kC1 e (triangle 0 T) (Sn n) u v - kIn e S u v‖ₑ ≤ D n u

/-- `S` is obtained by the construction of §4.5.3 from the datum `h`: it is the strong limit of
`C¹` solutions whose data have the same vertex value and converge to `h` in `W^{1,1}`. -/
def IsConstructedLimit (e T : ℝ) (h : ℝ → ℂ) (S : Fields) : Prop :=
  ∃ (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ), (∀ n, hn n 0 = h 0) ∧
    Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
    StrongLimit e T Sn S

end EmcsfAcExtension.Local
