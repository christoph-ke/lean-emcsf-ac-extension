/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Gap.AnnularFlux
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Fixed-ray budgets on complete triangles

These characteristic budgets retain both scalar and electric mass. They use
closed-section FTC, so no incoming flux density is evaluated outside its own
characteristic section. Source: charged_SF_new_version.tex:L1629–1671.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Annulus

/-- [internal] A continuous function starting below a level and ending above it
has a least hit, with strict inequality at every earlier parameter. -/
theorem first_hit {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (ha : f a < c) (hb : c < f b) :
    ∃ t ∈ Ioo a b, f t = c ∧ (∀ s ∈ Icc a t, f s ≤ c) ∧
      (∀ s ∈ Ico a t, f s < c) ∧ ∀ s ∈ Icc a b, f s = c → t ≤ s := by
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab.le hf ⟨ha.le, hb.le⟩
  let A : Set ℝ := {s ∈ Icc a b | f s = c}
  have hA : IsCompact A :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) (fun _ h => h.1)
  obtain ⟨t, htA, hleast⟩ := hA.exists_isLeast ⟨t, ht, hft⟩
  have hta : a < t := by
    refine lt_of_le_of_ne htA.1.1 ?_
    intro heq
    have : f a = c := heq.symm ▸ htA.2
    linarith
  have htb : t < b := by
    refine lt_of_le_of_ne htA.1.2 ?_
    intro heq
    have : f b = c := heq ▸ htA.2
    linarith
  have hbelow : ∀ s ∈ Icc a t, f s ≤ c := by
    intro s hs
    by_contra hsc
    have hcs : c < f s := lt_of_not_ge hsc
    have has : a < s := by
      refine lt_of_le_of_ne hs.1 ?_
      rintro rfl
      linarith
    obtain ⟨q, hq, hfq⟩ := intermediate_value_Icc has.le
      (hf.mono (Icc_subset_Icc le_rfl (hs.2.trans htb.le))) ⟨ha.le, hcs.le⟩
    have hqs : q < s := by
      refine lt_of_le_of_ne hq.2 ?_
      intro heq
      have : f s = c := heq ▸ hfq
      linarith
    have hqt : t ≤ q := hleast ⟨⟨hq.1, hq.2.trans (hs.2.trans htb.le)⟩, hfq⟩
    exact (not_lt_of_ge hqt) (hqs.trans_le hs.2)
  refine ⟨t, ⟨hta, htb⟩, htA.2, hbelow, ?_, fun s hs he => hleast ⟨hs, he⟩⟩
  intro s hs
  apply lt_of_le_of_ne (hbelow s ⟨hs.1, hs.2.le⟩)
  intro he
  exact (not_lt_of_ge (hleast ⟨⟨hs.1, hs.2.le.trans htb.le⟩, he⟩)) hs.2

/-- [node lem:charged-conditional-gap#near-trapped-first-exit]
An incoming ray reaches `1/256` at a least parameter before its existing axis
endpoint. Earlier gaps are strictly smaller; the threshold is universal. -/
theorem near_trapped_first_exit {e u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {a v₂ : ℝ}
    (ha : u₀ ≤ a) (hav : a < v₂) (hb : v₂ ≤ b)
    (hinit : 1 - S.mu a v₂ < 1 / 256) :
    ∃ τ ∈ Ioo a v₂, 1 - S.mu τ v₂ = 1 / 256 ∧
      (∀ u ∈ Icc a τ, 1 - S.mu u v₂ ≤ 1 / 256) ∧
      (∀ u ∈ Ico a τ, 1 - S.mu u v₂ < 1 / 256) ∧
      ∀ u ∈ Icc a v₂, 1 - S.mu u v₂ = 1 / 256 → τ ≤ u := by
  have hs : inSeg a v₂ v₂ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hav.le).2 ⟨ha, le_rfl, hb⟩
  have hc : ContinuousOn (fun u => 1 - S.mu u v₂) (Icc a v₂) :=
    continuousOn_const.sub (Calculus.continuousOn_in_section (Gap.continuousOn_mu hS) hs)
  apply first_hit hav hc hinit
  have hz := (hS.axis v₂ ⟨ha.trans hav.le, le_rfl, hb⟩).1
  simp only [Fields.mu, hz, div_zero, sub_zero]
  norm_num

/-- [internal] The closed-interval recovery API obtained from the least exit. -/
theorem first_recovery {e u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) {a v₂ : ℝ}
    (ha : u₀ ≤ a) (hav : a < v₂) (hb : v₂ ≤ b)
    (hinit : 1 - S.mu a v₂ < 1 / 256) :
    ∃ τ ∈ Ioo a v₂, 1 - S.mu τ v₂ = 1 / 256 ∧
      ∀ u ∈ Icc a τ, 1 - S.mu u v₂ ≤ 1 / 256 := by
  obtain ⟨τ, hτ, he, hc, _, _⟩ := near_trapped_first_exit hS ha hav hb hinit
  exact ⟨τ, hτ, he, hc⟩

/-- [internal] Positive expansion makes the radius strictly increase along
every nontrivial closed outgoing section, including an axis endpoint. -/
theorem radius_out_lt {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u ≤ a) (hab : a < b)
    (hs : outSeg u a b ⊆ D) : S.r u a < S.r u b := by
  have hf := (Calculus.out_integralForm hS hua hab.le hs).1
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on hf.1
    (fun v hv => hS.lam_pos (u, v) (hs ⟨rfl, hv.1.le, hv.2.le⟩)) hab
  rw [← hf.2] at hi
  exact sub_pos.mp hi

/-- [internal] Negative expansion makes the radius strictly decrease along
every nontrivial closed incoming section. -/
theorem radius_in_lt {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a < b) (hbv : b ≤ v)
    (hs : inSeg a b v ⊆ D) : S.r b v < S.r a v := by
  have hf := (Calculus.in_integralForm hS hab.le hbv hs).1
  have hi := intervalIntegral.intervalIntegral_pos_of_pos_on hf.1.neg
    (fun u hu => neg_pos.mpr (hS.nu_neg (u, v) (hs ⟨hu.1.le, hu.2.le, rfl⟩))) hab
  simp only [Pi.neg_apply] at hi
  rw [intervalIntegral.integral_neg, ← hf.2] at hi
  linarith only [hi]

/-- [internal] The incoming radius equation has its continuous prescribed
derivative at every interior parameter of a contained characteristic section. -/
theorem radius_in_hasDerivAt {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a t v u : ℝ} (htv : t ≤ v)
    (hs : inSeg a t v ⊆ D) (hu : u ∈ Ioo a t) :
    HasDerivAt (fun x => S.r x v) (S.nu u v) u := by
  apply Local.hasDerivAt_of_integralForm_interior hu
    ((Calculus.continuousOn_in_section hS.cont_nu hs).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd (hd.trans_le htv) (by
    rintro ⟨x, y⟩ ⟨hcx, hxd, rfl⟩
    exact hs ⟨hc.le.trans hcx, hxd.trans hd.le, rfl⟩)).1

/-- [internal] An exact logarithmic radius primitive, with any fixed shift
whose denominator stays positive on the entire characteristic section. -/
theorem shifted_radius_log_integral {e C : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a t v : ℝ} (hat : a ≤ t) (htv : t ≤ v)
    (hs : inSeg a t v ⊆ D)
    (hpos : ∀ u ∈ Icc a t, 0 < S.r u v - C) :
    (∫ u in a..t, -S.nu u v / (S.r u v - C)) =
      Real.log (S.r a v - C) - Real.log (S.r t v - C) := by
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cg : ContinuousOn (fun u => S.r u v - C) (Icc a t) := cr.sub continuousOn_const
  have cf : ContinuousOn (fun u => Real.log (S.r u v - C)) (Icc a t) :=
    cg.log (fun u hu => (hpos u hu).ne')
  have ci : IntervalIntegrable (fun u => S.nu u v / (S.r u v - C)) volume a t :=
    (cn.div cg (fun u hu => (hpos u hu).ne')).intervalIntegrable_of_Icc hat
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hat cf
    (fun u hu => ((radius_in_hasDerivAt hS htv hs hu).sub_const C).log
      (hpos u ⟨hu.1.le, hu.2.le⟩).ne') ci
  simp only [neg_div, intervalIntegral.integral_neg]
  linarith only [he]

/-- [internal] The radial optical sign makes the distance between two fixed
incoming rays nonincreasing, all the way to the inner future axis endpoint. -/
theorem fixed_ray_width_antitone_of_charge_bound {e u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hcharge : ∀ p ∈ triangle u₀ b, S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (_hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b) :
    AntitoneOn (fun u => S.r u v₂ - S.r u v₁) (Icc a v₁) := by
  intro x hx y hy hxy
  have hs₁ : inSeg x y v₁ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hxy).2 ⟨ha.trans hx.1, hy.2, hv.le.trans hb⟩
  have hs₂ : inSeg x y v₂ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hxy).2 ⟨ha.trans hx.1, hy.2.trans hv.le, hb⟩
  have hf₁ := (Calculus.in_integralForm hS hxy hy.2 hs₁).1
  have hf₂ := (Calculus.in_integralForm hS hxy (hy.2.trans hv.le) hs₂).1
  have hi : (∫ u in x..y, S.nu u v₂) ≤ ∫ u in x..y, S.nu u v₁ := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hxy hf₂.1 hf₁.1
    intro u hu
    have hs : outSeg u v₁ v₂ ⊆ triangle u₀ b :=
      (outSeg_subset_triangle_iff hv.le).2
        ⟨ha.trans (hx.1.trans hu.1.le), (hu.2.trans_le hy.2).le, hb⟩
    exact Gap.nu_out_antitone_of_charge_bound hS (hu.2.trans_le hy.2) hv.le hs
      (fun v hv' => hcharge (u, v) (hs ⟨rfl, hv'⟩))
  rw [← hf₁.2, ← hf₂.2] at hi
  linarith only [hi]

/-- [internal]
The outer ray reaches radius `2*d*R` strictly before the inner ray's future
axis endpoint. On the closed crossing interval the annulus is separated from
the axis and has width at most its inner radius. The optical charge premise
is the pointwise conclusion of `cg:relative-charge`. -/
theorem fixed_ray_crossing_of_charge_bound {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hcharge : ∀ p ∈ triangle u₀ b, S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1 / 2)
    (hinit : S.r a v₁ = (1 - d) * S.r a v₂) :
    ∃ σ ∈ Ioo a v₁, S.r σ v₂ = 2 * d * S.r a v₂ ∧
      (∀ t ∈ Icc a σ,
        S.r t v₂ ≥ 2 * d * S.r a v₂ ∧
        S.r t v₁ ≥ S.r t v₂ / 2 ∧
        S.r t v₁ ≥ d * S.r a v₂ ∧
        (S.r t v₂ - S.r t v₁) / S.r t v₁ ≤ 1) ∧
      (∀ t ∈ Icc a v₁, S.r t v₂ = 2 * d * S.r a v₂ → t = σ) := by
  have hR := hS.r_pos (a, v₂) ⟨ha, (hav.trans hv).le, hb⟩ (hav.trans hv)
  have hmono := fixed_ray_width_antitone_of_charge_bound hS hcharge ha hav hv hb
  have hwidth (t : ℝ) (ht : t ∈ Icc a v₁) :
      S.r t v₂ - S.r t v₁ ≤ d * S.r a v₂ := by
    have h := hmono ⟨le_rfl, hav.le⟩ ht ht.1
    dsimp only at h
    rw [hinit] at h
    nlinarith only [h]
  have haxis := (hS.axis v₁ ⟨ha.trans hav.le, le_rfl, hv.le.trans hb⟩).1
  have hs : inSeg a v₁ v₂ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hav.le).2 ⟨ha, hv.le, hb⟩
  have hc := Calculus.continuousOn_in_section hS.cont_r hs
  have hfinal := hwidth v₁ ⟨hav.le, le_rfl⟩
  rw [haxis, sub_zero] at hfinal
  have hstart : 2 * d * S.r a v₂ < S.r a v₂ := by nlinarith only [hR, hd.2]
  have hend : S.r v₁ v₂ < 2 * d * S.r a v₂ := by
    nlinarith only [hfinal, mul_pos hd.1 hR]
  obtain ⟨σ, hσ, hσr⟩ := intermediate_value_Icc' hav.le hc ⟨hend.le, hstart.le⟩
  have has : a < σ := by
    refine lt_of_le_of_ne hσ.1 ?_
    rintro rfl
    linarith only [hσr, hstart]
  have hsv : σ < v₁ := by
    refine lt_of_le_of_ne hσ.2 ?_
    intro heq
    rw [heq] at hσr
    linarith only [hσr, hend]
  have hanti : StrictAntiOn (fun t => S.r t v₂) (Icc a v₁) := by
    intro x hx y hy hxy
    exact radius_in_lt hS hxy (hy.2.trans hv.le)
      ((inSeg_subset_triangle_iff hxy.le).2 ⟨ha.trans hx.1, hy.2.trans hv.le, hb⟩)
  refine ⟨σ, ⟨has, hsv⟩, hσr, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ Icc a v₁ := ⟨ht.1, ht.2.trans hsv.le⟩
    have houter : 2 * d * S.r a v₂ ≤ S.r t v₂ := by
      rw [← hσr]
      exact hanti.antitoneOn ht' hσ ht.2
    have hw := hwidth t ht'
    have hinner : S.r t v₂ / 2 ≤ S.r t v₁ := by linarith only [hw, houter]
    have hpos : 0 < S.r t v₁ := by nlinarith only [hinner, houter, mul_pos hd.1 hR]
    refine ⟨houter, hinner, by linarith only [hinner, houter], ?_⟩
    apply (div_le_iff₀ hpos).2
    linarith only [hinner]
  · intro t ht heq
    exact hanti.injOn ht hσ (heq.trans hσr.symm)

/-- [node lem:charged-conditional-gap#fixed-ray-mass-budgets]
Before an inner incoming ray reaches its axis, its mass loss is at most its
initial mass and hence half the initial outer radius. The outer radius loss
is at most that initial radius. All coefficients are fixed and uniform in
the solution, coupling, triangle, and characteristic labels. -/
theorem fixed_ray_mass_budgets {e u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    {a t v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hat : a ≤ t) (htv : t < v₁)
    (hv : v₁ ≤ v₂) (hb : v₂ ≤ b) :
    (∫ u in a..t, -S.mU u v₁) ≤ S.m a v₁ ∧
      S.m a v₁ ≤ S.r a v₂ / 2 ∧
      (∫ u in a..t, -S.nu u v₂) ≤ S.r a v₂ := by
  have hp₁ : (a, v₁) ∈ triangle u₀ b := ⟨ha, hat.trans htv.le, hv.trans hb⟩
  have hpₜ : (t, v₁) ∈ triangle u₀ b := ⟨ha.trans hat, htv.le, hv.trans hb⟩
  have hp₂ : (t, v₂) ∈ triangle u₀ b := ⟨ha.trans hat, htv.le.trans hv, hb⟩
  have hs₁ : inSeg a t v₁ ⊆ triangle u₀ b := by
    rintro ⟨u, v⟩ ⟨hu, hut, rfl⟩
    exact ⟨ha.trans hu, hut.trans htv.le, hv.trans hb⟩
  have hs₂ : inSeg a t v₂ ⊆ triangle u₀ b := by
    rintro ⟨u, v⟩ ⟨hu, hut, rfl⟩
    exact ⟨ha.trans hu, hut.trans (htv.le.trans hv), hb⟩
  have hmform := (Gap.mass hS).2 a t v₁ hat htv.le hs₁
  have hrform := (Calculus.in_integralForm hS hat (htv.le.trans hv) hs₂).1
  have hmₜ : 0 ≤ S.m t v₁ := by
    have h := hmu (t, v₁) hpₜ
    have hr := hS.r_pos (t, v₁) hpₜ htv
    have h' := (le_div_iff₀ hr).mp h
    linarith only [h']
  have hma : S.m a v₁ < S.r a v₁ / 2 := by
    have hr := hS.r_pos (a, v₁) hp₁ (hat.trans_lt htv)
    have h := (div_lt_iff₀ hr).mp (sub_pos.mp (hS.one_sub_mu_pos (a, v₁) hp₁))
    linarith only [h]
  have hrad := Gap.radius_out_le hS (hat.trans htv.le) hv (by
    rintro ⟨u, v⟩ ⟨rfl, hv₁, hv₂⟩
    exact ⟨ha, (hat.trans htv.le).trans hv₁, hv₂.trans hb⟩)
  have hrₜ := (hS.r_pos (t, v₂) hp₂ (htv.trans_le hv)).le
  rw [intervalIntegral.integral_neg, ← hmform.2]
  rw [intervalIntegral.integral_neg, ← hrform.2]
  exact ⟨by linarith only [hmₜ], by linarith only [hma, hrad], by linarith only [hrₜ]⟩

/-- [internal] The actual conditional bootstrap discharges the optical charge
bound on the whole complete triangle, including its regular axis. -/
theorem triangle_charge_bound {e δ u₀ b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64) :
    ∀ p ∈ triangle u₀ b, S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 := by
  rintro ⟨u, v⟩ hp
  change u₀ ≤ u ∧ u ≤ v ∧ v ≤ b at hp
  change S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v
  rcases lt_or_eq_of_le hp.2.1 with huv | rfl
  · have hs : outSeg u u v ⊆ triangle u₀ b :=
      (outSeg_subset_triangle_iff huv.le).2 ⟨hp.1, le_rfl, hp.2.2⟩
    have h := Gap.relative_charge hS huv hs hδ (hmu (u, v) hp)
      (fun s hs' => hgap (u, s) (hs ⟨rfl, hs'⟩))
      (fun s hs' => hsmall (u, s) (hs ⟨rfl, hs'⟩))
    exact (h.1.trans h.2).trans (by nlinarith only [hmu (u, v) hp])
  · have hr := (hS.axis u hp).1
    simp [Fields.mu, hr]

/-- [internal] Fixed-ray crossing under exactly the conditional triangle bootstrap. Its
optical premise is derived by Gauss' law, with no extra hypothesis. -/
theorem fixed_ray_crossing {e δ u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1 / 2)
    (hinit : S.r a v₁ = (1 - d) * S.r a v₂) :
    ∃ σ ∈ Ioo a v₁, S.r σ v₂ = 2 * d * S.r a v₂ ∧
      (∀ t ∈ Icc a σ,
        S.r t v₂ ≥ 2 * d * S.r a v₂ ∧
        S.r t v₁ ≥ S.r t v₂ / 2 ∧
        S.r t v₁ ≥ d * S.r a v₂ ∧
        (S.r t v₂ - S.r t v₁) / S.r t v₁ ≤ 1) ∧
      (∀ t ∈ Icc a v₁, S.r t v₂ = 2 * d * S.r a v₂ → t = σ) :=
  fixed_ray_crossing_of_charge_bound hS (triangle_charge_bound hS hδ hmu hgap hsmall)
    ha hav hv hb hd hinit

/-- [node lem:charged-conditional-gap#fixed-ray-annulus-crossing]
The full fixed-ray crossing contract, including the supported width derivative,
closed-interval width monotonicity and bound, and all stopped radius bounds.
The coefficients are exact and uniform in all solution and annulus parameters. -/
theorem fixed_ray_annulus_crossing {e δ u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1 / 2) (hinit : S.r a v₁ = (1 - d) * S.r a v₂) :
    ∃ σ ∈ Ioo a v₁, S.r σ v₂ = 2 * d * S.r a v₂ ∧
      AntitoneOn (fun t => S.r t v₂ - S.r t v₁) (Icc a v₁) ∧
      (∀ t ∈ Icc a v₁, S.r t v₂ - S.r t v₁ ≤ d * S.r a v₂) ∧
      (∀ t ∈ Ioo a v₁,
        HasDerivAt (fun x => S.r x v₂ - S.r x v₁) (S.nu t v₂ - S.nu t v₁) t ∧
          S.nu t v₂ - S.nu t v₁ ≤ 0) ∧
      (∀ t ∈ Icc a σ,
        S.r t v₂ ≥ 2 * d * S.r a v₂ ∧ S.r t v₁ ≥ S.r t v₂ - d * S.r a v₂ ∧
        S.r t v₁ ≥ S.r t v₂ / 2 ∧ S.r t v₁ ≥ d * S.r a v₂ ∧
        (S.r t v₂ - S.r t v₁) / S.r t v₁ ≤ 1) ∧
      (∀ t ∈ Icc a v₁, S.r t v₂ = 2 * d * S.r a v₂ → t = σ) := by
  obtain ⟨σ, hσ, he, hgeom, huniq⟩ := fixed_ray_crossing hS hδ hmu hgap hsmall
    ha hav hv hb hd hinit
  have hc := triangle_charge_bound hS hδ hmu hgap hsmall
  have hm := fixed_ray_width_antitone_of_charge_bound hS hc ha hav hv hb
  have hw t (ht : t ∈ Icc a v₁) : S.r t v₂ - S.r t v₁ ≤ d * S.r a v₂ := by
    have hh := hm ⟨le_rfl, hav.le⟩ ht ht.1
    dsimp only at hh
    rw [hinit] at hh
    linarith only [hh]
  refine ⟨σ, hσ, he, hm, hw, ?_, ?_, huniq⟩
  · intro t ht
    have hs₁ : inSeg a v₁ v₁ ⊆ triangle u₀ b :=
      (inSeg_subset_triangle_iff hav.le).2 ⟨ha, le_rfl, hv.le.trans hb⟩
    have hs₂ : inSeg a v₁ v₂ ⊆ triangle u₀ b :=
      (inSeg_subset_triangle_iff hav.le).2 ⟨ha, hv.le, hb⟩
    have hs : outSeg t v₁ v₂ ⊆ triangle u₀ b :=
      (outSeg_subset_triangle_iff hv.le).2 ⟨ha.trans ht.1.le, ht.2.le, hb⟩
    exact ⟨(radius_in_hasDerivAt hS hv.le hs₂ ht).sub
      (radius_in_hasDerivAt hS le_rfl hs₁ ht), sub_nonpos.mpr
        (Gap.nu_out_antitone_of_charge_bound hS ht.2 hv.le hs (fun v hv => hc (t,v) (hs ⟨rfl,hv⟩)))⟩
  · intro t ht
    obtain ⟨ho, hi, hp, hrat⟩ := hgeom t ht
    exact ⟨ho, by linarith only [hw t ⟨ht.1, ht.2.trans hσ.2.le⟩], hi, hp, hrat⟩

/-- [internal] The annular width error has the exact logarithmic budget on
the fixed-ray crossing interval. Its coefficient is uniform in the radius,
the labels, the solution, and every `0 < d < 1/2`. -/
theorem fixed_ray_width_integral_bound {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hcharge : ∀ p ∈ triangle u₀ b,
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2)
    {a σ v₁ v₂ : ℝ} (ha : u₀ ≤ a) (haσ : a < σ) (hσv : σ < v₁)
    (hv : v₁ < v₂) (hb : v₂ ≤ b) (hd : 0 < d ∧ d < 1 / 2)
    (hinit : S.r a v₁ = (1 - d) * S.r a v₂)
    (hσr : S.r σ v₂ = 2 * d * S.r a v₂)
    (houter : ∀ u ∈ Icc a σ, 2 * d * S.r a v₂ ≤ S.r u v₂) :
    IntervalIntegrable (fun u => (-S.nu u v₂) *
      (S.r u v₂ - S.r u v₁) / S.r u v₁) volume a σ ∧
    (∫ u in a..σ, (-S.nu u v₂) * (S.r u v₂ - S.r u v₁) / S.r u v₁) ≤
      d * S.r a v₂ * Real.log ((1 - d) / d) := by
  have hav := haσ.trans hσv
  have hR := hS.r_pos (a, v₂) ⟨ha, (hav.trans hv).le, hb⟩ (hav.trans hv)
  have hDR : 0 < d * S.r a v₂ := mul_pos hd.1 hR
  have hs₁ : inSeg a σ v₁ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff haσ.le).2 ⟨ha, hσv.le, hv.le.trans hb⟩
  have hs₂ : inSeg a σ v₂ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff haσ.le).2 ⟨ha, hσv.le.trans hv.le, hb⟩
  have cr₁ := Calculus.continuousOn_in_section hS.cont_r hs₁
  have cr₂ := Calculus.continuousOn_in_section hS.cont_r hs₂
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs₂
  have hmono := fixed_ray_width_antitone_of_charge_bound hS hcharge ha hav hv hb
  have hwidth (u : ℝ) (hu : u ∈ Icc a σ) :
      S.r u v₂ - S.r u v₁ ≤ d * S.r a v₂ := by
    have h := hmono ⟨le_rfl, hav.le⟩ ⟨hu.1, hu.2.trans hσv.le⟩ hu.1
    dsimp only at h
    rw [hinit] at h
    nlinarith only [h]
  have hp₁ (u : ℝ) (hu : u ∈ Icc a σ) : 0 < S.r u v₁ :=
    hS.r_pos (u, v₁) (hs₁ ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hσv)
  have hden (u : ℝ) (hu : u ∈ Icc a σ) :
      0 < S.r u v₂ - d * S.r a v₂ := by
    have h := houter u hu
    linarith only [h, hDR]
  have cW : ContinuousOn (fun u => (-S.nu u v₂) *
      (S.r u v₂ - S.r u v₁) / S.r u v₁) (Icc a σ) :=
    (cn.neg.mul (cr₂.sub cr₁)).div cr₁ (fun u hu => (hp₁ u hu).ne')
  have cB : ContinuousOn (fun u => d * S.r a v₂ *
      (-S.nu u v₂ / (S.r u v₂ - d * S.r a v₂))) (Icc a σ) :=
    continuousOn_const.mul
      (cn.neg.div (cr₂.sub continuousOn_const) (fun u hu => (hden u hu).ne'))
  have hpoint (u : ℝ) (hu : u ∈ Icc a σ) :
      (-S.nu u v₂) * (S.r u v₂ - S.r u v₁) / S.r u v₁ ≤
        d * S.r a v₂ * (-S.nu u v₂ / (S.r u v₂ - d * S.r a v₂)) := by
    have hdenle : S.r u v₂ - d * S.r a v₂ ≤ S.r u v₁ := by
      linarith only [hwidth u hu]
    have hfrac := (div_le_div_of_nonneg_right (hwidth u hu) (hp₁ u hu).le).trans
      (div_le_div_of_nonneg_left hDR.le (hden u hu) hdenle)
    have hn := (neg_pos.mpr (hS.nu_neg (u, v₂) (hs₂ ⟨hu.1, hu.2, rfl⟩))).le
    calc
      _ = (-S.nu u v₂) * ((S.r u v₂ - S.r u v₁) / S.r u v₁) := by ring
      _ ≤ (-S.nu u v₂) * (d * S.r a v₂ / (S.r u v₂ - d * S.r a v₂)) :=
        mul_le_mul_of_nonneg_left hfrac hn
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on (μ := volume) haσ.le
    (cW.intervalIntegrable_of_Icc haσ.le) (cB.intervalIntegrable_of_Icc haσ.le) hpoint
  have hlog := shifted_radius_log_integral hS haσ.le (hσv.le.trans hv.le) hs₂ hden
  have hlog' : Real.log (S.r a v₂ - d * S.r a v₂) -
      Real.log (S.r σ v₂ - d * S.r a v₂) = Real.log ((1 - d) / d) := by
    rw [hσr]
    have hfirst : S.r a v₂ - d * S.r a v₂ = (1 - d) * S.r a v₂ := by ring
    have hlast : 2 * d * S.r a v₂ - d * S.r a v₂ = d * S.r a v₂ := by ring
    rw [hfirst, hlast, ← Real.log_div (mul_ne_zero (by linarith only [hd.2]) hR.ne') hDR.ne']
    congr 1
    field_simp [hd.1.ne', hR.ne']
  refine ⟨cW.intervalIntegrable_of_Icc haσ.le, ?_⟩
  simpa only [intervalIntegral.integral_const_mul, hlog, hlog'] using hi

/-- [internal] Integrating the charged annular
flux comparison to the fixed-ray crossing gives its strict mass bound.
The explicit flux premise is discharged by `cg:annular-flux`; all crossing,
mass, radius, and logarithmic budgets are proved here from `IsSolution`. -/
theorem annular_bound_of_flux_comparison {e u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b))
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hcharge : ∀ p ∈ triangle u₀ b,
      S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1 / 2)
    (hinit : S.r a v₁ = (1 - d) * S.r a v₂)
    (hflux : ∀ u ∈ Icc a v₁, u < v₁ →
      (S.r u v₂ - S.r u v₁) / S.r u v₁ ≤ 1 →
      (-S.mU u v₂) - (-S.mU u v₁) ≤
        (1 / 1024 : ℝ) * (-S.mU u v₁) +
        ((1 + 2 / 1024 : ℝ) / 2) *
          ((-S.nu u v₂) * (S.r u v₂ - S.r u v₁) / S.r u v₁) +
        (1 / 2048 : ℝ) * (-S.nu u v₂)) :
    2 * (S.m a v₂ - S.m a v₁) / S.r a v₂ <
      2 * d + 2 / 1024 + (1 + 2 / 1024) * d * Real.log ((1 - d) / d) := by
  obtain ⟨σ, hσ, hσr, hgeom, _⟩ :=
    fixed_ray_crossing_of_charge_bound hS hcharge ha hav hv hb hd hinit
  have hs₁ : inSeg a σ v₁ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hσ.1.le).2 ⟨ha, hσ.2.le, hv.le.trans hb⟩
  have hs₂ : inSeg a σ v₂ ⊆ triangle u₀ b :=
    (inSeg_subset_triangle_iff hσ.1.le).2 ⟨ha, hσ.2.le.trans hv.le, hb⟩
  have hm₁ := (Gap.mass hS).2 a σ v₁ hσ.1.le hσ.2.le hs₁
  have hm₂ := (Gap.mass hS).2 a σ v₂ hσ.1.le (hσ.2.le.trans hv.le) hs₂
  have hr₂ := (Calculus.in_integralForm hS hσ.1.le (hσ.2.le.trans hv.le) hs₂).1
  have hF₁ : IntervalIntegrable (fun u => -S.mU u v₁) volume a σ := hm₁.1.neg
  have hF₂ : IntervalIntegrable (fun u => -S.mU u v₂) volume a σ := hm₂.1.neg
  have hn₂ : IntervalIntegrable (fun u => -S.nu u v₂) volume a σ := hr₂.1.neg
  have hW := fixed_ray_width_integral_bound hS hcharge ha hσ.1 hσ.2 hv hb hd hinit
    hσr (fun u hu => (hgeom u hu).1)
  have hi := intervalIntegral.integral_mono_on hσ.1.le (hF₂.sub hF₁)
    (((hF₁.const_mul (1 / 1024)).add (hW.1.const_mul ((1 + 2 / 1024) / 2))).add
      (hn₂.const_mul (1 / 2048)))
    (fun u hu => hflux u ⟨hu.1, hu.2.trans hσ.2.le⟩ (hu.2.trans_lt hσ.2)
      (hgeom u hu).2.2.2)
  simp only [
    intervalIntegral.integral_sub hF₂ hF₁,
    intervalIntegral.integral_add
      ((hF₁.const_mul (1 / 1024)).add (hW.1.const_mul ((1 + 2 / 1024) / 2)))
      (hn₂.const_mul (1 / 2048)),
    intervalIntegral.integral_add (hF₁.const_mul (1 / 1024))
      (hW.1.const_mul ((1 + 2 / 1024) / 2)),
    intervalIntegral.integral_const_mul] at hi
  have hbds := fixed_ray_mass_budgets hS hmu ha hσ.1.le hσ.2 hv.le hb
  have hF₁eq : (∫ u in a..σ, -S.mU u v₁) = S.m a v₁ - S.m σ v₁ := by
    rw [intervalIntegral.integral_neg, ← hm₁.2]
    ring
  have hF₂eq : (∫ u in a..σ, -S.mU u v₂) = S.m a v₂ - S.m σ v₂ := by
    rw [intervalIntegral.integral_neg, ← hm₂.2]
    ring
  have hp₁ : (σ, v₁) ∈ triangle u₀ b :=
    ⟨ha.trans hσ.1.le, hσ.2.le, hv.le.trans hb⟩
  have hp₂ : (σ, v₂) ∈ triangle u₀ b :=
    ⟨ha.trans hσ.1.le, hσ.2.le.trans hv.le, hb⟩
  have hr₁pos := hS.r_pos (σ, v₁) hp₁ hσ.2
  have hr₂pos := hS.r_pos (σ, v₂) hp₂ (hσ.2.trans hv)
  have hm₁pos : 0 ≤ S.m σ v₁ := by
    have h := (le_div_iff₀ hr₁pos).mp (hmu (σ, v₁) hp₁)
    linarith only [h]
  have hm₂lt : 2 * S.m σ v₂ < S.r σ v₂ := by
    simpa only [one_mul] using
      (div_lt_iff₀ hr₂pos).mp (sub_pos.mp (hS.one_sub_mu_pos (σ, v₂) hp₂))
  have hR := hS.r_pos (a, v₂) ⟨ha, (hav.trans hv).le, hb⟩ (hav.trans hv)
  apply (div_lt_iff₀ hR).2
  rw [hF₁eq, hF₂eq] at hi
  have hlast : 2 * (S.m σ v₂ - S.m σ v₁) < 2 * d * S.r a v₂ := by
    rw [← hσr]
    linarith only [hm₁pos, hm₂lt]
  nlinarith only [hi, hbds.2.1, hbds.2.2, hW.2, hlast, hm₁pos]

/-- [node cg:annular-bound]
The strict charged annular mass bound under the actual conditional bootstrap.
Its constants are independent of the solution, coupling, bootstrap gap,
triangle, initial radius, and every fractional width `0 < d < 1/2`. -/
theorem annular_bound {e δ u₀ b d : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ p ∈ triangle u₀ b, 0 ≤ S.mu p.1 p.2)
    (hgap : ∀ p ∈ triangle u₀ b, δ ≤ 1 - S.mu p.1 p.2)
    (hsmall : ∀ p ∈ triangle u₀ b, |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ δ / 64)
    {a v₁ v₂ : ℝ} (ha : u₀ ≤ a) (hav : a < v₁) (hv : v₁ < v₂) (hb : v₂ ≤ b)
    (hd : 0 < d ∧ d < 1 / 2)
    (hinit : S.r a v₁ = (1 - d) * S.r a v₂) :
    2 * (S.m a v₂ - S.m a v₁) / S.r a v₂ <
      2 * d + 2 / 1024 + (1 + 2 / 1024) * d * Real.log ((1 - d) / d) := by
  apply annular_bound_of_flux_comparison hS hmu (triangle_charge_bound hS hδ hmu hgap hsmall)
    ha hav hv hb hd hinit
  intro u hu huv hwidth
  have hs : outSeg u u v₂ ⊆ triangle u₀ b :=
    (outSeg_subset_triangle_iff (huv.trans hv).le).2
      ⟨ha.trans hu.1, le_rfl, hb⟩
  have hf := Gap.annular_flux hS huv hv.le hs hδ
    (fun v hv' => hmu (u, v) (hs ⟨rfl, hv'⟩))
    (fun v hv' => hgap (u, v) (hs ⟨rfl, hv'⟩))
    (fun v hv' => hsmall (u, v) (hs ⟨rfl, hv'⟩)) hwidth
  convert hf using 1; ring

end EmcsfAcExtension.Global.Annulus
