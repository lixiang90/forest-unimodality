import ForestUnimodality.DirectionalMomentMonotonicity
import ForestUnimodality.SignedGaussian350JointData.AlphaFourNinthBeta65

/-! The complete joint-direction budget has a proved continuation from one
positive real endpoint to every larger mean free count. -/
namespace ForestUnimodality.JointDirectionBudget
open Real Set Finset UnboundedBudget DirectionalMomentMonotonicity
namespace Profile
noncomputable def gamma : ℝ := SignedGaussian350Profile.parameter
noncomputable def H : ℝ := SignedGaussianProfile.profile gamma 1
noncomputable def B : ℝ := SignedGaussian350JointData.AlphaFourNinthBeta65.B
noncomputable def weight (i : ℕ) : ℝ :=
  SignedGaussian350JointData.AlphaFourNinthBeta65.prices i-
    SignedGaussian350JointData.AlphaFourNinthBeta65.prices (i+1)
theorem gamma_pos : 0<gamma := SignedGaussian350Profile.parameter_bounds.1
theorem B_nonneg : 0≤B := by norm_num [B,SignedGaussian350JointData.AlphaFourNinthBeta65.B]
theorem weight_nonneg (i:ℕ) (hi:i<40) : 0≤weight i := by
  unfold weight
  by_cases h:i<39
  · exact sub_nonneg.mpr (SignedGaussian350JointData.AlphaFourNinthBeta65.prices_decreasing i h)
  · have he:i=39 := by omega
    subst i
    norm_num [SignedGaussian350JointData.AlphaFourNinthBeta65.prices]
end Profile

structure Parameters where
  start : ℝ
  v : ℝ
  V : ℝ
  eta : ℝ
  D : ℝ
  R : ℝ
  amp : ℝ
  lfactor : ℝ
  A : ℝ
  B : ℝ
  price : ℝ
  profileRate : ℕ→ℝ
  smallRate : ℕ→ℝ
  smallCoefficient : ℕ→ℝ

def Valid (p : Parameters) : Prop :=
  0<p.start ∧ 0<p.v ∧ 0<p.V ∧ 0≤p.eta ∧ 0≤p.D ∧ 0≤p.R ∧
  0≤p.amp ∧ 0≤p.lfactor ∧ 0≤p.A ∧ 0≤p.B ∧ 0≤p.price ∧
  1<(4/9)*p.start ∧ 1/2≤decayRate (4/9) p.v*p.start ∧
  (∀i<40,0≤p.profileRate i) ∧ (∀i<24,0≤p.smallRate i) ∧
  1/2≤p.smallRate 0*p.start ∧
  (∀i<23,0≤p.smallCoefficient i) ∧
  (∀i<22,p.smallCoefficient (i+1)≤p.smallCoefficient i)

noncomputable def curve (p : Parameters) (m : ℝ) : ℝ :=
  Profile.H-Profile.gamma*p.R/2-Profile.B*p.D/m-
    ∑i∈range 40,Profile.weight i*exp (-p.profileRate i*m)

noncomputable def finiteError (p : Parameters) (m : ℝ) : ℝ :=
  sqrt (2*Real.pi*p.V)*sqrt (uZero (4/9) p.v p.eta p.D m^2+
    (p.lfactor/m)*uZero (4/9) p.v p.eta p.D m*uTwo (4/9) p.v p.eta p.D m)

noncomputable def step (p : Parameters) (m : ℝ) : ℝ :=
  p.amp*(max 0 (-curve p m)/(2*p.v*m)+Profile.gamma/(24*p.v^2*m^2))

noncomputable def small (p : Parameters) (m : ℝ) : ℝ :=
  p.amp*sqrt (2*Real.pi*p.V)*
    (powerExpCost (1/2) (p.smallRate 0) m+
      (1/p.v)*(p.smallCoefficient 22*powerExpCost (-1/2) (p.smallRate 23) m+
        ∑i∈range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*
          powerExpCost (-1/2) (p.smallRate (i+1)) m))

noncomputable def main (p : Parameters) (m : ℝ) : ℝ :=
  99/100-p.A*p.R-p.B*p.D/m

noncomputable def polynomialCost (p : Parameters) (m : ℝ) : ℝ :=
  p.price*exp (-p.smallRate 23*m)

noncomputable def margin (p : Parameters) (m : ℝ) : ℝ :=
  main p m-polynomialCost p m-finiteError p m-step p m-small p m

theorem curve_monotoneOn {p : Parameters} (hp : Valid p) : MonotoneOn (curve p) (Ici p.start) := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  intro x hx y hy hxy
  unfold curve
  apply sub_le_sub
  · apply sub_le_sub_left
    exact div_le_div_of_nonneg_left (mul_nonneg Profile.B_nonneg hD) (hs.trans_le hx) hxy
  · apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (Profile.weight_nonneg i (mem_range.mp hi))
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hxy (hprofile i (mem_range.mp hi))]

theorem finiteError_antitoneOn {p : Parameters} (hp : Valid p) : AntitoneOn (finiteError p) (Ici p.start) := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  intro x hx y hy hxy
  have hx0:=hs.trans_le hx
  have hy0:=hs.trans_le hy
  have hax : 1<(4/9)*x := ham.trans_le (mul_le_mul_of_nonneg_left hx (by norm_num))
  have hay : 1<(4/9)*y := ham.trans_le (mul_le_mul_of_nonneg_left hy (by norm_num))
  have hu0:=uZero_antitoneOn (by norm_num : (0:ℝ)<4/9) hv heta hD hs ham hx hy hxy
  have hu2:=uTwo_antitoneOn (by norm_num : (0:ℝ)<4/9) hv heta hD hs ham hthreshold hx hy hxy
  have h0x:=uZero_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hx0 hax
  have h0y:=uZero_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hy0 hay
  have h2x:=uTwo_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hx0 hax
  have h2y:=uTwo_nonneg (by norm_num : (0:ℝ)<4/9) hv heta hD hy0 hay
  unfold finiteError
  apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
  apply sqrt_le_sqrt
  apply add_le_add (pow_le_pow_left₀ h0y hu0 2)
  apply mul_le_mul _ hu2 h2y (mul_nonneg (div_nonneg hlf hx0.le) h0x)
  exact mul_le_mul (div_le_div_of_nonneg_left hlf hx0 hxy) hu0 h0y (div_nonneg hlf hx0.le)

theorem step_antitoneOn {p : Parameters} (hp : Valid p) : AntitoneOn (step p) (Ici p.start) := by
  have hcurve:=curve_monotoneOn hp
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  intro x hx y hy hxy
  have hx0:=hs.trans_le hx
  have hy0:=hs.trans_le hy
  have hn : max 0 (-curve p y)≤max 0 (-curve p x) := max_le_max le_rfl (neg_le_neg (hcurve hx hy hxy))
  unfold step
  apply mul_le_mul_of_nonneg_left _ hamp
  apply add_le_add
  · exact div_le_div₀ (le_max_left _ _) hn (by positivity) (by gcongr)
  · apply div_le_div_of_nonneg_left Profile.gamma_pos.le (by positivity)
    gcongr

theorem small_antitoneOn {p : Parameters} (hp : Valid p) : AntitoneOn (small p) (Ici p.start) := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  intro x hx y hy hxy
  have he (i:ℕ) (hi:i<24) : powerExpCost (-1/2) (p.smallRate i) y≤powerExpCost (-1/2) (p.smallRate i) x :=
    powerExpCost_antitoneOn hs (hsmall i hi)
      (by nlinarith [mul_nonneg (hsmall i hi) hs.le]) hx hy hxy
  unfold small
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hamp (sqrt_nonneg _))
  apply add_le_add (powerExpCost_antitoneOn hs (hsmall 0 (by norm_num)) hsmall0 hx hy hxy)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left (he 23 (by norm_num)) (hC 22 (by norm_num)))
  apply sum_le_sum
  intro i hi
  have hi0:=mem_range.mp hi
  exact mul_le_mul_of_nonneg_left (he (i+1) (by omega)) (sub_nonneg.mpr (hCdec i hi0))

theorem margin_monotoneOn {p : Parameters} (hp : Valid p) : MonotoneOn (margin p) (Ici p.start) := by
  have hfinite:=finiteError_antitoneOn hp
  have hstep:=step_antitoneOn hp
  have hsmall':=small_antitoneOn hp
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  intro x hx y hy hxy
  unfold margin
  apply sub_le_sub (sub_le_sub (sub_le_sub ?_ (hfinite hx hy hxy)) (hstep hx hy hxy)) (hsmall' hx hy hxy)
  apply sub_le_sub
  · unfold main
    exact sub_le_sub_left (div_le_div_of_nonneg_left (mul_nonneg hB hD) (hs.trans_le hx) hxy) _
  · unfold polynomialCost
    apply mul_le_mul_of_nonneg_left _ hprice
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hxy (hsmall 23 (by norm_num))]

theorem margin_positive {p : Parameters} (hp : Valid p) (hbudget : 0<margin p p.start)
    {m : ℝ} (hm : p.start≤m) : 0<margin p m :=
  hbudget.trans_le (margin_monotoneOn hp (by simp only [Set.mem_Ici]; exact le_refl p.start) (show m∈Ici p.start from hm) hm)

#print axioms curve_monotoneOn
#print axioms margin_monotoneOn
#print axioms margin_positive
end ForestUnimodality.JointDirectionBudget
