import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! The actual one-dimensional minimization behind the signed Gaussian
curvature envelope. The parameter is arbitrary and positive; in particular
the contact points 2/5 and 9/20 belong to the same real-domain statement. -/
namespace ForestUnimodality.SignedGaussianMinimum
open Set Real Filter
open scoped Topology

noncomputable def slope (x : ℝ) : ℝ := (3 - 2 * x) * exp (-x)
noncomputable def normalized (p x : ℝ) : ℝ := (1 - 2 * x) * exp (-x) + p * x
noncomputable def objective (c y x : ℝ) : ℝ :=
  y ^ (-(3 / 2 : ℝ)) * (1 - 2 * x) * exp (-x) + c * y * x

theorem slope_hasDerivAt (x : ℝ) : HasDerivAt slope ((2 * x - 5) * exp (-x)) x := by
  have h := ((hasDerivAt_const x (3 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)).mul
    ((hasDerivAt_id x).neg.exp)
  convert! h using 1
  dsimp [slope]
  ring

theorem normalized_hasDerivAt (p x : ℝ) :
    HasDerivAt (normalized p) (p - slope x) x := by
  have h := (((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul 2)).mul
    ((hasDerivAt_id x).neg.exp)).add ((hasDerivAt_id x).const_mul p)
  convert! h using 1
  dsimp [normalized, slope]
  ring

theorem slope_strictAnti : StrictAntiOn slope (Icc 0 (3 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun x _ => (slope_hasDerivAt x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Icc 0 (3 / 2 : ℝ) := interior_subset hx
    rw [(slope_hasDerivAt x).deriv]
    exact mul_neg_of_neg_of_pos (by linarith [hx'.2]) (exp_pos _)

theorem slope_nonpos {x : ℝ} (hx : 3 / 2 ≤ x) : slope x ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_pos _).le

theorem slope_lt_three {x : ℝ} (hx : 0 < x) : slope x < 3 := by
  by_cases h : x ≤ 3 / 2
  · simpa [slope] using slope_strictAnti (by norm_num : (0 : ℝ) ∈ Icc 0 (3 / 2))
      ⟨hx.le, h⟩ hx
  · exact lt_of_le_of_lt (slope_nonpos (le_of_not_ge h)) (by norm_num)

theorem exists_unique_stationary {p : ℝ} (hp : 0 < p) (hp3 : p < 3) :
    ∃! u, u ∈ Ioo (0 : ℝ) (3 / 2) ∧ slope u = p := by
  have hcont : ContinuousOn slope (Icc (0 : ℝ) (3 / 2)) :=
    fun x _ => (slope_hasDerivAt x).continuousAt.continuousWithinAt
  have ht : p ∈ Icc (slope (3 / 2)) (slope 0) := by
    norm_num [slope]
    exact ⟨hp.le, hp3.le⟩
  obtain ⟨u, hu, heu⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 3 / 2) hcont ht
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := le_antisymm (le_of_not_gt hn) hu.1
    subst u
    norm_num [slope] at heu
    linarith
  have hu3 : u < 3 / 2 := by
    by_contra hn
    have he : u = 3 / 2 := le_antisymm hu.2 (le_of_not_gt hn)
    subst u
    norm_num [slope] at heu
    linarith
  refine ⟨u, ⟨⟨hu0, hu3⟩, heu⟩, ?_⟩
  intro v hv
  exact slope_strictAnti.injOn ⟨hv.1.1.le, hv.1.2.le⟩ hu (hv.2.trans heu.symm)

theorem normalized_strictMono_of_three_le {p : ℝ} (hp : 3 ≤ p) :
    StrictMonoOn (normalized p) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun x _ => (normalized_hasDerivAt p x).continuousAt.continuousWithinAt
  · intro x hx
    have hx0 : 0 < x := by simpa using hx
    rw [(normalized_hasDerivAt p x).deriv]
    linarith [slope_lt_three hx0]

theorem normalized_strictAnti_before {p u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) (he : slope u = p) :
    StrictAntiOn (normalized p) (Icc 0 u) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun x _ => (normalized_hasDerivAt p x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo 0 u := by simpa using hx
    rw [(normalized_hasDerivAt p x).deriv]
    have hl := slope_strictAnti ⟨hx'.1.le, (hx'.2.trans hu.2).le⟩
      ⟨hu.1.le, hu.2.le⟩ hx'.2
    linarith

theorem normalized_strictMono_after {p u : ℝ} (hp : 0 < p)
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) (he : slope u = p) :
    StrictMonoOn (normalized p) (Ici u) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun x _ => (normalized_hasDerivAt p x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : u < x := by simpa using hx
    rw [(normalized_hasDerivAt p x).deriv]
    by_cases hx3 : x ≤ 3 / 2
    · have hl := slope_strictAnti ⟨hu.1.le, hu.2.le⟩
        ⟨(hu.1.trans hx').le, hx3⟩ hx'
      linarith
    · have hl := slope_nonpos (le_of_not_ge hx3)
      linarith

theorem stationary_strict_minimum {p u : ℝ} (hp : 0 < p)
    (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) (he : slope u = p)
    {x : ℝ} (hx : 0 ≤ x) (hne : x ≠ u) : normalized p u < normalized p x := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact normalized_strictAnti_before hu he ⟨hx, h.le⟩ ⟨hu.1.le, le_rfl⟩ h
  · exact normalized_strictMono_after hp hu he (mem_Ici.mpr (le_refl u))
      (mem_Ici.mpr h.le) h

/-- Existence and uniqueness concern the actual objective on the entire
half-line, not merely its critical points on a bounded interval. -/
theorem exists_unique_normalized_minimum {p : ℝ} (hp : 0 < p) :
    ∃! u, 0 ≤ u ∧ ∀ x, 0 ≤ x → normalized p u ≤ normalized p x := by
  by_cases hp3 : p < 3
  · obtain ⟨u, hu, _⟩ := exists_unique_stationary hp hp3
    have hs : ∀ {x : ℝ}, 0 ≤ x → x ≠ u → normalized p u < normalized p x :=
      stationary_strict_minimum hp hu.1 hu.2
    refine ⟨u, ⟨hu.1.1.le, ?_⟩, ?_⟩
    · intro x hx
      by_cases he : x = u
      · subst x; exact le_rfl
      · exact (hs hx he).le
    · intro v hv
      by_contra hne
      exact (not_lt_of_ge (hv.2 u hu.1.1.le)) (hs hv.1 hne)
  · have hs := normalized_strictMono_of_three_le (le_of_not_gt hp3)
    refine ⟨0, ⟨le_rfl, ?_⟩, ?_⟩
    · intro x hx
      exact hs.monotoneOn (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx
    · intro v hv
      by_contra hne
      have hv0 : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hne)
      exact (not_lt_of_ge (hv.2 0 le_rfl))
        (hs (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hv.1) hv0)

theorem objective_eq_scaled {y : ℝ} (hy : 0 < y) (c x : ℝ) :
    objective c y x = y ^ (-(3 / 2 : ℝ)) * normalized (c * y ^ (5 / 2 : ℝ)) x := by
  have hp : y ^ (-(3 / 2 : ℝ)) * y ^ (5 / 2 : ℝ) = y := by
    rw [← Real.rpow_add hy]
    norm_num
  calc
    objective c y x = y ^ (-(3 / 2 : ℝ)) * (1 - 2 * x) * exp (-x) +
        c * (y ^ (-(3 / 2 : ℝ)) * y ^ (5 / 2 : ℝ)) * x := by rw [hp]; rfl
    _ = _ := by unfold normalized; ring

theorem exists_unique_objective_minimum {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ∃! u, 0 ≤ u ∧ ∀ x, 0 ≤ x → objective c y u ≤ objective c y x := by
  have hp : 0 < c * y ^ (5 / 2 : ℝ) := mul_pos hc (Real.rpow_pos_of_pos hy _)
  obtain ⟨u, hu, hunique⟩ := exists_unique_normalized_minimum hp
  have hscale : 0 < y ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hy _
  refine ⟨u, ⟨hu.1, ?_⟩, ?_⟩
  · intro x hx
    rw [objective_eq_scaled hy, objective_eq_scaled hy]
    exact mul_le_mul_of_nonneg_left (hu.2 x hx) hscale.le
  · intro v hv
    apply hunique v
    refine ⟨hv.1, ?_⟩
    intro x hx
    have hh := hv.2 x hx
    rw [objective_eq_scaled hy, objective_eq_scaled hy] at hh
    exact (mul_le_mul_iff_right₀ hscale).mp hh

/-- A genuine minimizer, specified on every positive slope parameter. -/
noncomputable def point (p : ℝ) : ℝ :=
  if hp : 0 < p then (exists_unique_normalized_minimum hp).choose else 0

theorem point_minimum {p : ℝ} (hp : 0 < p) :
    0 ≤ point p ∧ ∀ x, 0 ≤ x → normalized p (point p) ≤ normalized p x := by
  rw [point, dif_pos hp]
  exact (exists_unique_normalized_minimum hp).choose_spec.1

theorem point_eq_of_minimum {p u : ℝ} (hp : 0 < p)
    (hu : 0 ≤ u ∧ ∀ x, 0 ≤ x → normalized p u ≤ normalized p x) : point p = u := by
  rw [point, dif_pos hp]
  exact ((exists_unique_normalized_minimum hp).choose_spec.2 u hu).symm

theorem point_eq_zero {p : ℝ} (hp : 3 ≤ p) : point p = 0 := by
  apply point_eq_of_minimum (by linarith : 0 < p)
  refine ⟨le_rfl, ?_⟩
  intro x hx
  exact (normalized_strictMono_of_three_le hp).monotoneOn
    (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hx) hx

theorem point_stationary {p : ℝ} (hp : 0 < p) (hp3 : p < 3) :
    point p ∈ Ioo (0 : ℝ) (3 / 2) ∧ slope (point p) = p := by
  obtain ⟨u, hu, _⟩ := exists_unique_stationary hp hp3
  have he : point p = u := by
    apply point_eq_of_minimum hp
    refine ⟨hu.1.1.le, ?_⟩
    intro x hx
    by_cases hxu : x = u
    · subst x; exact le_rfl
    · exact (stationary_strict_minimum hp hu.1 hu.2 hx hxu).le
  simpa only [he] using hu

theorem point_slope {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) (3 / 2)) : point (slope u) = u := by
  have hp : 0 < slope u := mul_pos (by linarith [hu.2]) (exp_pos _)
  have h := point_stationary hp (slope_lt_three hu.1)
  exact slope_strictAnti.injOn ⟨h.1.1.le, h.1.2.le⟩ ⟨hu.1.le, hu.2.le⟩ h.2

theorem slope_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt slope ((2 * x - 5) * exp (-x)) x := by
  have h := ((hasStrictDerivAt_const (x := x) (3 : ℝ)).sub
    ((hasStrictDerivAt_id (x := x)).const_mul 2)).mul
      ((hasStrictDerivAt_id (x := x)).neg.exp)
  convert! h using 1
  dsimp [slope]
  ring

/-- The derivative is proved for the actual selected minimum using the
inverse function theorem, rather than postulated as an implicit equation. -/
theorem point_hasDerivAt {p : ℝ} (hp : 0 < p) (hp3 : p < 3) :
    HasDerivAt point (((2 * point p - 5) * exp (-point p))⁻¹) p := by
  have hu := point_stationary hp hp3
  have hn : (2 * point p - 5) * exp (-point p) ≠ 0 :=
    mul_ne_zero (by linarith [hu.1.2]) (exp_ne_zero _)
  have hi : ∀ᶠ x in 𝓝 (point p), point (slope x) = x := by
    filter_upwards [isOpen_Ioo.mem_nhds hu.1] with x hx
    exact point_slope hx
  have hd := (slope_hasStrictDerivAt (point p)).to_local_left_inverse hn hi
  rw [hu.2] at hd
  exact hd.hasDerivAt

theorem point_upper {p : ℝ} (hp : 0 < p) : point p ≤ max 0 ((3 - p) / 2) := by
  by_cases hp3 : p < 3
  · have hu := point_stationary hp hp3
    have he : exp (-point p) ≤ 1 := exp_le_one_iff.mpr (by linarith [hu.1.1])
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 3 - 2 * point p by linarith [hu.1.2])
    change slope (point p) ≤ (3 - 2 * point p) * 1 at hm
    rw [hu.2] at hm
    exact (show point p ≤ (3 - p) / 2 by linarith).trans (le_max_right _ _)
  · rw [point_eq_zero (le_of_not_gt hp3)]
    exact le_max_left _ _

theorem point_continuousAt_three : ContinuousAt point 3 := by
  change Tendsto point (𝓝 (3 : ℝ)) (𝓝 (point 3))
  rw [point_eq_zero (le_refl 3)]
  have hu : Tendsto (fun p : ℝ => max 0 ((3 - p) / 2)) (𝓝 3) (𝓝 0) := by
    simpa using (show ContinuousAt (fun p : ℝ => max 0 ((3 - p) / 2)) 3 by fun_prop).tendsto
  apply tendsto_const_nhds.squeeze' hu
  · filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 3)] with p hp
    exact (point_minimum hp).1
  · filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 3)] with p hp
    exact point_upper hp

theorem point_continuousAt {p : ℝ} (hp : 0 < p) : ContinuousAt point p := by
  rcases lt_trichotomy p 3 with h | h | h
  · exact (point_hasDerivAt hp h).continuousAt
  · subst p
    exact point_continuousAt_three
  · change Tendsto point (𝓝 p) (𝓝 (point p))
    rw [point_eq_zero h.le]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_nhds h] with q hq
    exact (point_eq_zero hq.le).symm

#print axioms exists_unique_stationary
#print axioms exists_unique_normalized_minimum
#print axioms exists_unique_objective_minimum
#print axioms point_hasDerivAt
#print axioms point_continuousAt
end ForestUnimodality.SignedGaussianMinimum
