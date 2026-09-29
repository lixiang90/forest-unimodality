import ForestUnimodality.SignedGaussianContact
import ForestUnimodality.SignedGaussianSlices

/-! Exact analytic interfaces for the two stage-350 profile certificates.
Numerical witnesses only bracket the genuine optimizer and its value. -/
namespace ForestUnimodality.SignedGaussian350Profile
open Real Set SignedGaussianMinimum SignedGaussianProfile SignedGaussianHermite

noncomputable def parameter : ℝ := (21/10)*exp (-(9/20:ℝ))

theorem parameter_bounds : 0<parameter ∧ parameter<3 := by
  have h:=SignedGaussianContact.contact_parameter (x₀:=9/20) (by norm_num)
  norm_num [SignedGaussianMinimum.slope,parameter] at h ⊢
  exact h

theorem profile_one : profile parameter 1=(209/200:ℝ)*exp (-(9/20:ℝ)) :=
  SignedGaussianContact.source_350_contact.2.1

theorem first_one : first parameter 1=(159/200:ℝ)*exp (-(9/20:ℝ)) :=
  SignedGaussianContact.source_350_contact.2.2

theorem profile_lower_sqrt {y u A : ℝ} (hy : 0<y) (hy1 : y≤1)
    (hu : u∈Icc (0:ℝ) (3/2))
    (hslope : (3-2*u)*exp (-u)≤parameter*(y*y*sqrt y))
    (hA : A≤((1+u-2*u^2)*exp (-u))/(y*sqrt y)) : A≤profile parameter y := by
  have hc:=parameter_bounds
  have hp : y^(5/2:ℝ)=y*y*sqrt y := by
    rw [show (5/2:ℝ)=2+1/2 by norm_num,rpow_add hy,rpow_two,←sqrt_eq_rpow]
    ring
  have hm : y^(-(3/2:ℝ))=1/(y*sqrt y) := by
    rw [rpow_neg hy.le,show (3/2:ℝ)=1+1/2 by norm_num,rpow_add hy,rpow_one,←sqrt_eq_rpow]
    simp only [one_div]
  have hbranch : parameter*y^(5/2:ℝ)<3 :=
    (mul_le_of_le_one_right hc.1.le (rpow_le_one hy.le hy1 (by norm_num))).trans_lt hc.2
  have hs : SignedGaussianMinimum.slope u≤parameter*y^(5/2:ℝ) := by
    simpa only [SignedGaussianMinimum.slope,hp] using hslope
  have h:=profile_lower_of_slope_bound hc.1 hy hbranch hu hs
  rw [hm] at h
  unfold contactValue at h
  convert! hA.trans (by convert! h using 1; ring) using 1

theorem gap_le_of_profile_lower {y A U B : ℝ}
    (hA : A≤profile parameter y) (hU : 0≤U)
    (hgap : (209/200:ℝ)*exp (-(9/20:ℝ))+
      (159/200:ℝ)*exp (-(9/20:ℝ))*(y-1)-B*(y-1)^2-A≤U) :
    positiveGap parameter (-B) y≤U := by
  unfold positiveGap quadratic
  rw [profile_one,first_one]
  apply max_le hU
  linarith

theorem coefficient_lower {beta A B : ℝ} (hb : 0<beta) (hb1 : beta<1)
    (hA : A≤profile parameter beta)
    (hmargin : (209/200:ℝ)*exp (-(9/20:ℝ))+
      (159/200:ℝ)*exp (-(9/20:ℝ))*(beta-1)-B*(beta-1)^2≤A) :
    -B≤coefficient parameter beta := by
  rw [SignedGaussianContact.coefficient_eq_quotient parameter_bounds.1 parameter_bounds.2 hb hb1,
    profile_one,first_one]
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0<1-beta))).mpr
  nlinarith

#print axioms profile_lower_sqrt
#print axioms gap_le_of_profile_lower
#print axioms coefficient_lower
end ForestUnimodality.SignedGaussian350Profile
