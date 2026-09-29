import ForestUnimodality.JointDirectionGraph
import ForestUnimodality.JointDirectionBudget
import ForestUnimodality.GaussianDirectionalCatalogue

/-! The fixed signed profile is averaged on the genuine graph law, at
all real displacements needed by the finite directional step. -/
namespace ForestUnimodality.JointDirectionProfileGraph
open Real Finset JointDirectionBudget GaussianDirectionFiniteStep
open ShiftedLayerMoments
namespace Data
open SignedGaussian350JointData.AlphaFourNinthBeta65 SignedGaussian350Profile

theorem first_nonneg : 0≤SignedGaussianProfile.first parameter 1 := by
  rw [first_one]; positivity

theorem bad_nonpos : SignedGaussianProfile.profile parameter 1+
    SignedGaussianProfile.first parameter 1*((4/9:ℝ)-1)-B*((4/9:ℝ)-1)^2≤0 := by
  rw [profile_one,first_one]
  have he : exp (-(9/20:ℝ))≤1 := exp_le_one_iff.mpr (by norm_num)
  norm_num [B]
  nlinarith [exp_pos (-(9/20:ℝ))]
end Data

variable {V:Type*} [DecidableEq V]

theorem actual_curve (p:Parameters) (hp:Valid p)
    (G:SimpleGraph V) (S I:Finset V) (hIS:I⊆S) (hI:G.IsIndepSet (I:Set V))
    {z m k v:ℝ} (hz:0<z) (hm:m=hardCoreAvailableMean G S I z) (hm0:0<m)
    (hmean:hardCoreMean G S z=k) (hv:0<v)
    (hvarL:hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤p.R*(v*m))
    (hvarM:hardCoreAvailableVariance G S I z≤p.D*m)
    (htail:∀i<40,hardCoreAvailableLowerTail G S I z
      (SignedGaussian350JointData.AlphaFourNinthBeta65.cuts (i+1)*m)≤exp (-p.profileRate i*m))
    (t:ℝ) :
    curve p m-Profile.gamma*t^2/2≤hardCoreLayerExpectation G S I z
      (fun j M=>if (4/9)*m≤(M:ℝ) then SignedGaussianLayerBudget.kernel
        (ratio m 0 M) (offset z m 0 k v j M+t) else 0) := by
  rcases hp with ⟨hs,hpv,hV,heta,hD,hR,rest⟩
  have h:=shifted_curvature_lower G S I hIS hI hz hm hm0 hmean hv hR hD
    SignedGaussian350Profile.parameter_bounds.1 SignedGaussian350Profile.parameter_bounds.2
    (alpha:=4/9) (beta:=13/20) (K:= -Profile.B) (by norm_num) (by norm_num) (by norm_num)
    SignedGaussian350JointData.AlphaFourNinthBeta65.curvature_lower
    (neg_nonpos.mpr Profile.B_nonneg) Data.first_nonneg (by simpa only [Profile.B,neg_mul,sub_eq_add_neg] using Data.bad_nonpos) hvarL hvarM
    SignedGaussian350JointData.AlphaFourNinthBeta65.cuts
    SignedGaussian350JointData.AlphaFourNinthBeta65.prices p.profileRate 39
    SignedGaussian350JointData.AlphaFourNinthBeta65.cuts_start
    SignedGaussian350JointData.AlphaFourNinthBeta65.cuts_end
    (fun i _=>SignedGaussian350JointData.AlphaFourNinthBeta65.cuts_steps i)
    SignedGaussian350JointData.AlphaFourNinthBeta65.prices_upper
    SignedGaussian350JointData.AlphaFourNinthBeta65.prices_decreasing
    SignedGaussian350JointData.AlphaFourNinthBeta65.prices_end
    (fun i hi=>by simpa only [neg_mul,mul_neg,mul_comm] using htail i (by omega)) t
  simp only [neg_mul,mul_neg,mul_comm] at h
  convert! h using 1
  all_goals (try simp only [curve,Profile.H,Profile.gamma,Profile.B,Profile.weight])
  all_goals ring_nf
  all_goals simp only [add_comm]

#print axioms Data.bad_nonpos
#print axioms actual_curve
end ForestUnimodality.JointDirectionProfileGraph
