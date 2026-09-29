import ForestUnimodality.SignedGaussianMinimum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The genuine minimum profile used by the signed Gaussian lower envelope.
All derivatives are tied to the real minimizer of SignedGaussianMinimum. -/
namespace ForestUnimodality.SignedGaussianProfile
open Set Real SignedGaussianMinimum

noncomputable def arg (c y : ℝ) : ℝ := point (c * y ^ (5 / 2 : ℝ))
noncomputable def profile (c y : ℝ) : ℝ := objective c y (arg c y)
noncomputable def velocity (y u : ℝ) : ℝ := (5 / 2 : ℝ) * (3 - 2 * u) / (y * (2 * u - 5))
noncomputable def first (c y : ℝ) : ℝ :=
  -(3 / 2 : ℝ) * y ^ (-(5 / 2 : ℝ)) * (1 - 2 * arg c y) * exp (-arg c y) + c * arg c y
noncomputable def second (c y : ℝ) : ℝ :=
  y ^ (-(7 / 2 : ℝ)) * exp (-arg c y) *
    (5 * (4 * arg c y ^ 2 - 12 * arg c y + 15)) / (2 * (2 * arg c y - 5))
noncomputable def third (c y : ℝ) : ℝ :=
  y ^ (-(9 / 2 : ℝ)) * exp (-arg c y) *
    (-5 * (16 * arg c y ^ 4 - 128 * arg c y ^ 3 + 360 * arg c y ^ 2 -
      600 * arg c y + 525)) / (2 * (2 * arg c y - 5) ^ 3)

theorem arg_continuousAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : ContinuousAt (arg c) y := by
  have hp := Real.continuousAt_rpow_const y (5 / 2 : ℝ) (Or.inl hy.ne')
  exact (point_continuousAt (mul_pos hc (rpow_pos_of_pos hy (5 / 2 : ℝ)))).comp'
    (f := fun t : ℝ => c * t ^ (5 / 2 : ℝ)) (hp.const_mul c)

theorem profile_continuousAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ContinuousAt (profile c) y := by
  have ha := arg_continuousAt hc hy
  have hp := Real.continuousAt_rpow_const y (-(3 / 2 : ℝ)) (Or.inl hy.ne')
  exact ((hp.mul ((continuousAt_const (y := (1 : ℝ))).sub (ha.const_mul 2))).mul
    (Real.continuous_exp.continuousAt.comp ha.neg)).add
    (((continuousAt_id (x := y)).const_mul c).mul ha)

theorem first_continuousAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : ContinuousAt (first c) y := by
  have ha := arg_continuousAt hc hy
  have hp := Real.continuousAt_rpow_const y (-(5 / 2 : ℝ)) (Or.inl hy.ne')
  exact ((((hp.const_mul (-(3 / 2 : ℝ))).mul
    ((continuousAt_const (y := (1 : ℝ))).sub (ha.const_mul 2))).mul
      (Real.continuous_exp.continuousAt.comp ha.neg)).add (ha.const_mul c))

theorem arg_stationary {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) :
    arg c y ∈ Ioo (0 : ℝ) (3 / 2) ∧ SignedGaussianMinimum.slope (arg c y) = c * y ^ (5 / 2 : ℝ) :=
  point_stationary (mul_pos hc (rpow_pos_of_pos hy _)) hbranch

theorem profile_lower {c y : ℝ} (hc : 0 < c) (hy : 0 < y) {x : ℝ} (hx : 0 ≤ x) :
    profile c y ≤ objective c y x := by
  have h := point_minimum (mul_pos hc (rpow_pos_of_pos hy (5 / 2 : ℝ)))
  unfold profile arg
  rw [objective_eq_scaled hy, objective_eq_scaled hy]
  exact mul_le_mul_of_nonneg_left (h.2 x hx) (rpow_pos_of_pos hy _).le

theorem profile_outer {c y : ℝ} (hbranch : 3 ≤ c * y ^ (5 / 2 : ℝ)) :
    profile c y = y ^ (-(3 / 2 : ℝ)) := by
  simp [profile, arg, point_eq_zero hbranch, objective]

noncomputable def contactValue (u : ℝ) : ℝ := (1 + u - 2 * u ^ 2) * exp (-u)

theorem contactValue_hasDerivAt (u : ℝ) :
    HasDerivAt contactValue (u * (2 * u - 5) * exp (-u)) u := by
  have h := (((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).sub
    (((hasDerivAt_id u).pow 2).const_mul 2)).mul ((hasDerivAt_id u).neg.exp)
  convert! h using 1
  dsimp [contactValue]
  ring

theorem contactValue_strictAnti : StrictAntiOn contactValue (Icc (0 : ℝ) (3 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · exact fun u _ => (contactValue_hasDerivAt u).continuousAt.continuousWithinAt
  · intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) (3 / 2) := by simpa using hu
    rw [(contactValue_hasDerivAt u).deriv]
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hu'.1 (by linarith [hu'.2])) (exp_pos _)

theorem profile_stationary_value {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) :
    profile c y = y ^ (-(3 / 2 : ℝ)) * contactValue (arg c y) := by
  have hu := arg_stationary hc hy hbranch
  unfold profile
  rw [objective_eq_scaled hy, ← hu.2]
  unfold normalized SignedGaussianMinimum.slope contactValue
  ring

theorem profile_lower_of_slope_bound {c y u : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) (hu : u ∈ Icc (0 : ℝ) (3 / 2))
    (hbound : SignedGaussianMinimum.slope u ≤ c * y ^ (5 / 2 : ℝ)) :
    y ^ (-(3 / 2 : ℝ)) * contactValue u ≤ profile c y := by
  have hp := arg_stationary hc hy hbranch
  have harg : arg c y ≤ u := by
    by_contra hn
    have ht := slope_strictAnti hu ⟨hp.1.1.le, hp.1.2.le⟩ (lt_of_not_ge hn)
    rw [hp.2] at ht
    exact (not_lt_of_ge hbound) ht
  rw [profile_stationary_value hc hy hbranch]
  exact mul_le_mul_of_nonneg_left
    (contactValue_strictAnti.antitoneOn ⟨hp.1.1.le, hp.1.2.le⟩ hu harg)
    (rpow_pos_of_pos hy _).le

theorem first_outer {c y : ℝ} (hbranch : 3 ≤ c * y ^ (5 / 2 : ℝ)) :
    first c y = -(3 / 2 : ℝ) * y ^ (-(5 / 2 : ℝ)) := by
  simp [first, arg, point_eq_zero hbranch]

private theorem rpow_five_halves {y : ℝ} (hy : 0 < y) :
    y ^ (5 / 2 : ℝ) = y ^ (3 / 2 : ℝ) * y := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, rpow_add hy, rpow_one]

theorem arg_hasDerivAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) :
    HasDerivAt (arg c) (velocity y (arg c y)) y := by
  have hu := arg_stationary hc hy hbranch
  have hdy : HasDerivAt (fun t : ℝ => c * t ^ (5 / 2 : ℝ))
      (c * ((5 / 2 : ℝ) * y ^ (3 / 2 : ℝ))) y := by
    convert! ((hasDerivAt_id y).rpow_const (p := (5 / 2 : ℝ)) (Or.inl hy.ne')).const_mul c using 1
    norm_num
  have hd := (point_hasDerivAt (mul_pos hc (rpow_pos_of_pos hy _)) hbranch).comp y hdy
  have hstation : (3 - 2 * arg c y) * exp (-arg c y) = c * (y ^ (3 / 2 : ℝ) * y) := by
    simpa [SignedGaussianMinimum.slope, rpow_five_halves hy] using hu.2
  have hden : 2 * arg c y - 5 ≠ 0 := by linarith [hu.1.2]
  convert! hd using 1
  change velocity y (arg c y) =
    ((2 * arg c y - 5) * exp (-arg c y))⁻¹ * (c * ((5 / 2 : ℝ) * y ^ (3 / 2 : ℝ)))
  unfold velocity
  field_simp [hy.ne', hden, exp_ne_zero]
  nlinarith [hstation]

theorem profile_hasDerivAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : HasDerivAt (profile c) (first c y) y := by
  have hu := arg_stationary hc hy hbranch
  have hd := arg_hasDerivAt hc hy hbranch
  have hp : HasDerivAt (fun t : ℝ => t ^ (-(3 / 2 : ℝ)))
      (-(3 / 2 : ℝ) * y ^ (-(5 / 2 : ℝ))) y := by
    convert! (hasDerivAt_id y).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hy.ne') using 1
    norm_num
  have hpow : y ^ (-(3 / 2 : ℝ)) * y ^ (5 / 2 : ℝ) = y := by
    rw [← rpow_add hy]
    norm_num
  have hcancel : y ^ (-(3 / 2 : ℝ)) * ((3 - 2 * arg c y) * exp (-arg c y)) = c * y := by
    rw [← SignedGaussianMinimum.slope, hu.2]
    calc
      _ = c * (y ^ (-(3 / 2 : ℝ)) * y ^ (5 / 2 : ℝ)) := by ring
      _ = c * y := by rw [hpow]
  have h := ((hp.mul ((hasDerivAt_const y (1 : ℝ)).sub (hd.const_mul 2))).mul
    hd.neg.exp).add (((hasDerivAt_id y).const_mul c).mul hd)
  convert! h using 1
  dsimp [profile, objective, first]
  linear_combination velocity y (arg c y) * hcancel

theorem parameter_eq {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) :
    c = y ^ (-(5 / 2 : ℝ)) * (3 - 2 * arg c y) * exp (-arg c y) := by
  have hu := arg_stationary hc hy hbranch
  have he : y ^ (-(5 / 2 : ℝ)) * y ^ (5 / 2 : ℝ) = 1 := by
    rw [← rpow_add hy]
    norm_num
  calc
    c = c * (y ^ (-(5 / 2 : ℝ)) * y ^ (5 / 2 : ℝ)) := by rw [he]; ring
    _ = y ^ (-(5 / 2 : ℝ)) * (c * y ^ (5 / 2 : ℝ)) := by ring
    _ = _ := by rw [← hu.2]; unfold SignedGaussianMinimum.slope; ring

theorem first_hasDerivAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : HasDerivAt (first c) (second c y) y := by
  have hu := arg_stationary hc hy hbranch
  have hd := arg_hasDerivAt hc hy hbranch
  have hp : HasDerivAt (fun t : ℝ => t ^ (-(5 / 2 : ℝ)))
      (-(5 / 2 : ℝ) * y ^ (-(7 / 2 : ℝ))) y := by
    convert! (hasDerivAt_id y).rpow_const (p := -(5 / 2 : ℝ)) (Or.inl hy.ne') using 1
    norm_num
  have h := ((((hp.const_mul (-(3 / 2 : ℝ))).mul
    ((hasDerivAt_const y (1 : ℝ)).sub (hd.const_mul 2))).mul hd.neg.exp).add (hd.const_mul c))
  have hcval := parameter_eq hc hy hbranch
  have hpow : y ^ (-(5 / 2 : ℝ)) = y ^ (-(7 / 2 : ℝ)) * y := by
    rw [show -(5 / 2 : ℝ) = -(7 / 2 : ℝ) + 1 by norm_num, rpow_add hy, rpow_one]
  have hden : 2 * arg c y - 5 ≠ 0 := by linarith [hu.1.2]
  convert! h using 1
  dsimp [first, second, velocity]
  generalize arg c y = u at *
  rw [hcval, hpow]
  field_simp [hy.ne', hden]
  ring

theorem second_hasDerivAt {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : HasDerivAt (second c) (third c y) y := by
  have hu := arg_stationary hc hy hbranch
  have hd := arg_hasDerivAt hc hy hbranch
  have hp : HasDerivAt (fun t : ℝ => t ^ (-(7 / 2 : ℝ)))
      (-(7 / 2 : ℝ) * y ^ (-(9 / 2 : ℝ))) y := by
    convert! (hasDerivAt_id y).rpow_const (p := -(7 / 2 : ℝ)) (Or.inl hy.ne') using 1
    norm_num
  have hn := ((((hd.pow 2).const_mul 4).sub (hd.const_mul 12)).add_const 15).const_mul 5
  have hden : 2 * arg c y - 5 ≠ 0 := by linarith [hu.1.2]
  have h := (((hp.mul hd.neg.exp).mul hn).div
    (((hd.const_mul 2).sub_const 5).const_mul 2) (mul_ne_zero (by norm_num) hden))
  have hpow : y ^ (-(7 / 2 : ℝ)) = y ^ (-(9 / 2 : ℝ)) * y := by
    rw [show -(7 / 2 : ℝ) = -(9 / 2 : ℝ) + 1 by norm_num, rpow_add hy, rpow_one]
  convert! h using 1
  dsimp [second, third, velocity]
  rw [hpow]
  field_simp [hy.ne', hden]
  ring

theorem second_neg {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : second c y < 0 := by
  have hu := arg_stationary hc hy hbranch
  have hq : 0 < 4 * arg c y ^ 2 - 12 * arg c y + 15 := by
    nlinarith [sq_nonneg (2 * arg c y - 3)]
  unfold second
  apply div_neg_of_pos_of_neg
  · exact mul_pos (mul_pos (rpow_pos_of_pos hy _) (exp_pos _)) (mul_pos (by norm_num) hq)
  · linarith [hu.1.2]

theorem third_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hbranch : c * y ^ (5 / 2 : ℝ) < 3) : 0 < third c y := by
  have hu := arg_stationary hc hy hbranch
  have hz : 0 ≤ (3 / 2 : ℝ) - arg c y := by linarith [hu.1.2]
  have hq : 0 < 16 * arg c y ^ 4 - 128 * arg c y ^ 3 + 360 * arg c y ^ 2 -
      600 * arg c y + 525 := by
    have he : 16 * arg c y ^ 4 - 128 * arg c y ^ 3 + 360 * arg c y ^ 2 -
        600 * arg c y + 525 =
      16 * ((3 / 2 : ℝ) - arg c y) ^ 4 + 32 * ((3 / 2 : ℝ) - arg c y) ^ 3 +
        168 * ((3 / 2 : ℝ) - arg c y) + 84 := by ring
    rw [he]
    positivity
  have hden : 2 * arg c y - 5 < 0 := by linarith [hu.1.2]
  unfold third
  apply div_pos_of_neg_of_neg
  · exact mul_neg_of_pos_of_neg (mul_pos (rpow_pos_of_pos hy _) (exp_pos _))
      (mul_neg_of_neg_of_pos (by norm_num) hq)
  · apply mul_neg_of_pos_of_neg (by norm_num)
    rw [pow_succ]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hden.ne) hden

#print axioms profile_lower
#print axioms arg_hasDerivAt
#print axioms profile_hasDerivAt
#print axioms first_hasDerivAt
#print axioms second_hasDerivAt
#print axioms third_pos
#print axioms profile_continuousAt
#print axioms first_continuousAt
#print axioms profile_lower_of_slope_bound
end ForestUnimodality.SignedGaussianProfile
