import ForestUnimodality.JointDirectionActual
import ForestUnimodality.ProbabilityDirectionBudget

/-! Orientation check: the negative lattice shift is the increasing
coefficient direction, and the positive shift is the decreasing direction. -/
namespace ForestUnimodality.JointDirectionCoefficient
open JointDirectionBudget JointDirectionActual ReciprocalGradientBudget
variable {V:Type*} [DecidableEq V] {p:Parameters} {G:SimpleGraph V} {S I:Finset V}
  {z m t:ℝ} {k:ℕ} {P:ℕ→GradientProfile}

theorem left (hp:Valid p) (he:Envelope p t) (h:Inputs p G S I z m z t k true P)
    (hb:0<margin p p.start) : countIndependent G S (k-1)<countIndependent G S k := by
  have hraw:=actual_positive hp he h hb
  simp only [if_true] at hraw
  have hpos:0<tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by
    have hid : (1+z)*tiltedLeft (countIndependent G S) z (partitionFunction G S z) k=
        tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
          z*tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k-1) := by
      unfold tiltedLeft
      have hz:1+z≠0:=ne_of_gt (by linarith [h.activity_pos])
      field_simp
      ring
    rw [←hid] at hraw
    exact pos_of_mul_pos_right hraw (by linarith [h.activity_pos])
  exact ProbabilityDirectionBudget.left_coefficient_lt _ h.activity_pos
    (partitionFunction_pos G S h.activity_pos.le) h.rank_pos hpos

theorem right (hp:Valid p) (he:Envelope p t) (h:Inputs p G S I z m (1/z) t k false P)
    (hb:0<margin p p.start) : countIndependent G S (k+1)<countIndependent G S k := by
  have hraw:=actual_positive hp he h hb
  simp only [Bool.false_eq_true,if_false] at hraw
  have hpos:0<tiltedRight (countIndependent G S) z (partitionFunction G S z) k := by
    have hid : tiltedRight (countIndependent G S) z (partitionFunction G S z) k=
        (z/(1+z))*(tiltedProbability (countIndependent G S) z (partitionFunction G S z) k-
          (1/z)*tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1)) := by
      unfold tiltedRight
      have hz:1+z≠0:=ne_of_gt (by linarith [h.activity_pos])
      have hz0:=h.activity_pos.ne'
      field_simp
      ring
    rw [hid]
    exact mul_pos (div_pos h.activity_pos (by linarith [h.activity_pos])) hraw
  exact ProbabilityDirectionBudget.right_coefficient_lt _ h.activity_pos
    (partitionFunction_pos G S h.activity_pos.le) k hpos

#print axioms left
#print axioms right
end ForestUnimodality.JointDirectionCoefficient
