module

public import EmcsfAcExtension.Global.Closure.Parameters
public import EmcsfAcExtension.Global.Closure.Clock
import EmcsfAcExtension.Global.Closure.Windows

/-! # Excluding the proper terminal row in a capped stage

These consumers apply to the actual finite boundary returned by a capped
cylinder or connector append. The strict-stop consumer accepts the literal
output of finite stopping continuation. The quantitative consumer instead
uses the clock and optical estimates of radius-stop improvement directly.
Source: `charged_SF_new_version.tex:L4079–L4083`, `charged_SF_new_version.tex:L4104–L4106`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
At a strictly stopped finite endpoint the cylinder's terminal-row
alternative is impossible. This consumes the exact literal strict-stop
predicate produced by `actual_finite_stopping_continuation_of_estimates`
or `strict_finite_stops_of_small_entry`. Constants: none. -/
theorem prescribed_clock_of_strict_cutoff {S : Fields}
    {ui u₀ R₀ δ c Λ F ε εstop x t T b : ℝ} {vb J Svar : ℝ → ℝ}
    (hx : u₀ ≤ x)
    (hstop : StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop x)
    (hb : S.r b 0 = R₀ / 2) (halt : t = T ∨ x = b) : t = T := by
  rcases halt with hfull | rfl
  · exact hfull
  · have hr := hstop.2.2.1 x ⟨hx, le_rfl⟩
    rw [hb] at hr
    exact (lt_irrefl _ hr).elim

/-- [internal]
The literal strict stop excludes the terminal-row branch of
`terminal_radius_cap`, leaving the target incoming connector endpoint.
Constants: none. -/
theorem connector_target_of_strict_cutoff {S : Fields}
    {ui u₀ R₀ δ c Λ F ε εstop x b : ℝ} {vb J Svar : ℝ → ℝ}
    (hx : u₀ ≤ x)
    (hstop : StrictFiniteCutoffStops S ui u₀ R₀ vb J Svar δ c Λ F ε εstop x)
    (halt : x = b ∨ S.r x 0 = R₀ / 2) : x = b := by
  rcases halt with hfull | hterminal
  · exact hfull
  · have hr := hstop.2.2.1 x ⟨hx, le_rfl⟩
    rw [hterminal] at hr
    exact (lt_irrefl _ hr).elim

end EmcsfAcExtension.Global.Closure
