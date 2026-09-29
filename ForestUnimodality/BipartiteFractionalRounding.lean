import ForestUnimodality.MarginalIndependent
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! Exact threshold rounding of an edge-feasible fractional independent
set. Integration is over explicit finite intervals, not an assumed random
independent-set representation. Vertex weights may have either sign. -/
namespace ForestUnimodality

open Finset MeasureTheory

namespace BipartiteFractionalRounding

def thresholdRegion (side : Fin 2) (x : ℝ) : Set ℝ :=
  if side.val = 0 then Set.Icc 0 x else Set.Ioc (1 - x) 1

theorem thresholdRegion_subset {side : Fin 2} {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    thresholdRegion side x ⊆ Set.Icc 0 1 := by
  unfold thresholdRegion
  split_ifs
  · exact fun _ ht => ⟨ht.1, ht.2.trans hx.2⟩
  · intro t ht
    exact ⟨by linarith [ht.1, hx.2], ht.2⟩

theorem thresholdRegion_measurable (side : Fin 2) (x : ℝ) :
    MeasurableSet (thresholdRegion side x) := by
  unfold thresholdRegion
  split_ifs <;> measurability

theorem thresholdRegion_integrable (side : Fin 2) (x w : ℝ) :
    Integrable ((thresholdRegion side x).indicator (fun _ : ℝ => w)) := by
  apply (integrable_indicator_iff (thresholdRegion_measurable side x)).mpr
  refine integrableOn_const ?_ (by finiteness)
  unfold thresholdRegion
  split_ifs <;> simp [Real.volume_Icc, Real.volume_Ioc]

theorem thresholdRegion_integral (side : Fin 2) {x : ℝ} (hx : x ∈ Set.Icc 0 1) (w : ℝ) :
    (∫ t : ℝ, (thresholdRegion side x).indicator (fun _ : ℝ => w) t) = w * x := by
  rw [integral_indicator_const w (thresholdRegion_measurable side x)]
  unfold thresholdRegion
  split_ifs
  · rw [Real.volume_real_Icc_of_le hx.1]
    simp [smul_eq_mul, mul_comm]
  · rw [Real.volume_real_Ioc_of_le (by linarith [hx.1] : 1 - x ≤ 1)]
    simp [smul_eq_mul, mul_comm]

end BipartiteFractionalRounding

open BipartiteFractionalRounding

variable {V : Type*} [DecidableEq V]

/-- Every maximum-weight independent set dominates every feasible
fractional independent set on a bipartite graph. -/
theorem IsMaximumWeightedIndependentOn.fractional_bound
    {G : SimpleGraph V} {S I : Finset V} {w : V → ℝ}
    (hI : IsMaximumWeightedIndependentOn G S I w) (hG : G.IsBipartite)
    (x : V → ℝ) (hx : ∀ v ∈ S, x v ∈ Set.Icc 0 1)
    (hedge : ∀ u ∈ S, ∀ v ∈ S, G.Adj u v → x u + x v ≤ 1) :
    (∑ v ∈ S, w v * x v) ≤ ∑ v ∈ I, w v := by
  classical
  obtain ⟨c⟩ := hG
  let J (t : ℝ) : Finset V := S.filter (fun v => t ∈ thresholdRegion (c v) (x v))
  have hJ (t : ℝ) : J t ∈ independentSubsets G S := by
    refine mem_independentSubsets.mpr ⟨filter_subset _ _, ?_⟩
    intro u hu v hv _ hadj
    obtain ⟨huS, hut⟩ := mem_filter.mp hu
    obtain ⟨hvS, hvt⟩ := mem_filter.mp hv
    have hedge' := hedge u huS v hvS hadj
    have hne : (c u).val ≠ (c v).val := fun h => c.valid hadj (Fin.ext h)
    by_cases hcu : (c u).val = 0
    · by_cases hcv : (c v).val = 0
      · exact hne (hcu.trans hcv.symm)
      · simp only [thresholdRegion, if_pos hcu, if_neg hcv, Set.mem_Icc, Set.mem_Ioc] at hut hvt
        linarith [hut.2, hvt.1]
    · by_cases hcv : (c v).val = 0
      · simp only [thresholdRegion, if_neg hcu, if_pos hcv, Set.mem_Icc, Set.mem_Ioc] at hut hvt
        linarith [hut.1, hvt.2]
      · have hu2 := (c u).isLt
        have hv2 := (c v).isLt
        omega
  let f (v : V) : ℝ → ℝ := (thresholdRegion (c v) (x v)).indicator (fun _ => w v)
  let W : ℝ := ∑ v ∈ I, w v
  let upper : ℝ → ℝ := (Set.Icc (0 : ℝ) 1).indicator (fun _ => W)
  have hf (v : V) : Integrable (f v) := thresholdRegion_integrable _ _ _
  have hu : Integrable upper := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hpoint (t : ℝ) : (∑ v ∈ S, f v t) ≤ upper t := by
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have hsum : (∑ v ∈ S, f v t) = ∑ v ∈ J t, w v := by
        simp only [J, sum_filter, f, Set.indicator_apply]
      rw [hsum]
      exact (hI.2 _ (hJ t)).trans_eq (by simp [upper, ht, W])
    · have hz : (∑ v ∈ S, f v t) = 0 := by
        apply sum_eq_zero
        intro v hv
        have hnot : t ∉ thresholdRegion (c v) (x v) := fun h =>
          ht (thresholdRegion_subset (hx v hv) h)
        simp [f, hnot]
      simp [hz, upper, ht]
  have hint := integral_mono (integrable_finsetSum S (fun v _ => hf v)) hu hpoint
  rw [integral_finsetSum S (fun v _ => hf v)] at hint
  have he (v : V) (hv : v ∈ S) : (∫ t : ℝ, f v t) = w v * x v :=
    thresholdRegion_integral _ (hx v hv) _
  have hupper : (∫ t : ℝ, upper t) = W := by
    rw [show upper = (Set.Icc (0 : ℝ) 1).indicator (fun _ : ℝ => W) from rfl,
      integral_indicator_const W measurableSet_Icc, Real.volume_real_Icc_of_le (by norm_num)]
    simp
  simpa only [sum_congr rfl he, hupper, W] using hint

#print axioms IsMaximumWeightedIndependentOn.fractional_bound

end ForestUnimodality
