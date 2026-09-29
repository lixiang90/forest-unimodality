import ForestUnimodality.FlowUniformBounds
import ForestUnimodality.AffineSourceLibrary
import ForestUnimodality.TiltedSourceLibrary
import ForestUnimodality.Stage99MarkedSourceLibrary

namespace ForestUnimodality.FlowVarianceSources
open Set

inductive Source where
  | uniform : Fin 16→Source
  | support : Fin 15→Source
  | tilted : Fin 36→Source
  | marked : Fin 31→Source
  deriving DecidableEq

def Source.D : Source→ℚ→ℚ→ℚ
  | .uniform i,beta,_ => (NonnegativeSourceLibrary.parameters i).A*beta
  | .support i,beta,_ => (AffineSourceLibrary.parameters i).A*beta
  | .tilted _,_,_ => 0
  | .marked i,_,U => (Stage99MarkedSourceLibrary.parameters i).A*U

def Source.C : Source→ℚ
  | .uniform _ => 0
  | .support i => (AffineSourceLibrary.parameters i).C
  | .tilted i => (TiltedSourceLibrary.parameters i).C
  | .marked i => (Stage99MarkedSourceLibrary.parameters i).C

def Source.needsMean : Source→Bool
  | .marked _ => true
  | _ => false

def Source.Covers : Source→ℝ→ℝ→ℝ→ℝ→Prop
  | .uniform i,_,b,_,_ => b≤((NonnegativeSourceLibrary.parameters i).b:ℝ)
  | .support i,_,b,_,_ => b≤((AffineSourceLibrary.domain i).b:ℝ)
  | .tilted i,_,b,start,_ => b≤((TiltedSourceLibrary.domain0 i).b:ℝ) ∧
      b*Real.exp (-start)≤((TiltedSourceLibrary.domain1 i).b:ℝ)
  | .marked i,a,b,_,finish => ((Stage99MarkedSourceLibrary.domain i).lower:ℝ)≤a*Real.exp (-finish) ∧
      b≤((Stage99MarkedSourceLibrary.domain i).b:ℝ)

theorem Source.C_nonneg (s : Source) : (0:ℝ)≤s.C := by
  cases s with
  | uniform i => simp [Source.C]
  | support i => exact (AffineSourceLibrary.C_pos i).le
  | tilted i => exact (TiltedSource.Parameters.check_sound (TiltedSourceLibrary.parameters_checked i)).2.le
  | marked i => exact (Stage99MarkedSourceLibrary.coefficients_nonneg i).2

variable {V : Type*} [DecidableEq V]

theorem Source.actual_variance (s : Source) {beta U : ℚ}
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S B : Finset V)
    (hBS : B⊆S) (hB : G.IsIndepSet (B:Set V)) {z a b start finish m : ℝ}
    (ha : 0<a) (hzlo : a≤z) (hzhi : z≤b) (hstart : 0≤start)
    (hcover : s.Covers a b start finish) (hcard : (B.card:ℝ)≤m*(beta:ℝ))
    (hmu : s.needsMean=true → ∀t∈Icc start finish, FixedIndependentTilt.totalMean G S B z t≤m*(U:ℝ)) :
    ∀t∈Icc start finish, FixedIndependentTilt.markedVariance G S B z t≤
      m*(s.D beta U:ℝ)+(s.C:ℝ)*FixedIndependentTilt.markedMean G S B z t := by
  have hz := ha.trans_le hzlo
  have hins : FixedIndependentTilt.inside B=(fun J : Finset V=>((J∩B).card:ℝ)) := rfl
  cases s with
  | uniform i =>
    intro t ht
    have hact : ∀x∈S, 0 ≤ independentTiltActivities B z (Real.exp (-t)) x ∧
        independentTiltActivities B z (Real.exp (-t)) x≤((NonnegativeSourceLibrary.parameters i).b:ℝ) := by
      intro x _
      have he := Real.exp_le_one_iff.mpr (by linarith [ht.1] : -t≤0)
      unfold independentTiltActivities
      split_ifs
      · exact ⟨by positivity,(by nlinarith : Real.exp (-t)*z≤z).trans (hzhi.trans hcover)⟩
      · exact ⟨hz.le,hzhi.trans hcover⟩
    have hh := NonnegativeSourceLibrary.actual_variance i G hG S B hBS _ hact
    have hA := (NonnegativeSource.Parameters.check_sound (NonnegativeSourceLibrary.parameters_checked i)).A_nonneg
    have hc := mul_le_mul_of_nonneg_left hcard hA
    simp only [FixedIndependentTilt.markedVariance,FixedIndependentTilt.weight_eq_heterogeneous,
      hins,Source.D,Source.C,Rat.cast_mul,Rat.cast_zero,zero_mul,add_zero]
    simp only [heterogeneousVariance] at hh
    nlinarith
  | support i =>
    intro t ht
    have hh := AffineSourceLibrary.actual_tilt i G hG S B hBS hz (hzhi.trans hcover) t (hstart.trans ht.1)
    have hA := (AffineSource.Parameters.check_sound (AffineSourceLibrary.parameters_checked i)).2.1
    have hc := mul_le_mul_of_nonneg_left hcard hA
    change ((AffineSourceLibrary.parameters i).A:ℝ)*(B.card:ℝ)≤
      ((AffineSourceLibrary.parameters i).A:ℝ)*(m*(beta:ℝ)) at hc
    simp only [FixedIndependentTilt.markedVariance,FixedIndependentTilt.markedMean,
      FixedIndependentTilt.weight_eq_heterogeneous,hins,
      Source.D,Source.C,Rat.cast_mul]
    simp only [heterogeneousVariance,heterogeneousMean] at hh
    nlinarith
  | tilted i =>
    intro t ht
    have hh := TiltedSourceLibrary.actual_variance i G hG S B hB hz (hzhi.trans hcover.1)
      ((mul_le_mul_of_nonneg_right hzhi (Real.exp_pos _).le).trans hcover.2) ht.1
    simpa only [Source.D,Source.C,Rat.cast_zero,mul_zero,zero_add] using hh
  | marked i =>
    have hh := Stage99MarkedSourceLibrary.variance_on_step i G hG S B hB ha hzlo hzhi hstart
      hcover.1 hcover.2 (hmu rfl)
    simpa only [Source.D,Source.C,Rat.cast_mul] using hh

#print axioms Source.C_nonneg
#print axioms Source.actual_variance
end ForestUnimodality.FlowVarianceSources
