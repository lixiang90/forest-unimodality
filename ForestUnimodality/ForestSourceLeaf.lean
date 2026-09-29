import ForestUnimodality.HeterogeneousHardCore
import ForestUnimodality.ForestLeaf

/-! Exact heterogeneous leaf elimination for signed source observables.
The residual activity is changed at the leaf's unique neighbor. This is an
identity for the actual finite independent-set distribution, not an assumption
about messages. Numeric forest source bounds are not asserted here. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def leafReducedActivities (activity : V → ℝ) (v u : V) : V → ℝ :=
  Function.update activity u (activity u / (1 + activity v))

noncomputable def leafReducedMarks (activity a : V → ℝ) (v u : V) : V → ℝ :=
  Function.update a u (a u - a v * (activity v / (1 + activity v)))

noncomputable def leafConditionalMean (p : ℝ) (v u : V)
    (F : Finset V → ℝ) (J : Finset V) : ℝ :=
  if u ∈ J then F J else (1 - p) * F J + p * F (insert v J)

theorem leafReducedActivities_nonneg (activity : V → ℝ) (S : Finset V) {v u : V}
    (hv : v ∈ S) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∀ x ∈ S.erase v, 0 ≤ leafReducedActivities activity v u x := by
  intro x hx
  by_cases hxu : x = u
  · subst x
    simp only [leafReducedActivities, Function.update_self]
    exact div_nonneg (hactivity u (mem_of_mem_erase hx)) (by linarith [hactivity v hv])
  · simpa only [leafReducedActivities, Function.update_of_ne hxu] using
      hactivity x (mem_of_mem_erase hx)

theorem weight_leafReducedActivities (activity : V → ℝ) (v u : V)
    (hden : 1 + activity v ≠ 0) (J : Finset V) :
    heterogeneousWeight activity J =
      heterogeneousWeight (leafReducedActivities activity v u) J *
        (if u ∈ J then 1 + activity v else 1) := by
  classical
  by_cases hu : u ∈ J
  · rw [if_pos hu]
    unfold heterogeneousWeight leafReducedActivities
    rw [prod_update_of_mem hu]
    have hp : (∏ x ∈ J, activity x) = activity u * ∏ x ∈ J \ {u}, activity x := by
      simpa only [Function.update_eq_self] using prod_update_of_mem hu activity (activity u)
    rw [hp]
    field_simp
  · simp only [if_neg hu, mul_one, heterogeneousWeight, leafReducedActivities,
      prod_update_of_notMem hu]

theorem independentSubsets_leaf_deleted (G : SimpleGraph V) (S : Finset V) {v u : V}
    (hadj : G.Adj v u) (hleaf : ∀ x ∈ S, G.Adj v x → x = u) :
    independentSubsets G (S \ closedNeighborhoodIn G S v) =
      (independentSubsets G (S.erase v)).filter (fun J => u ∉ J) := by
  classical
  ext J
  simp only [mem_filter, mem_independentSubsets]
  constructor
  · rintro ⟨hJS, hJ⟩
    refine ⟨⟨?_, hJ⟩, ?_⟩
    · intro x hx
      obtain ⟨hxS, hxv, _⟩ := mem_sdiff_closedNeighborhoodIn.mp (hJS hx)
      exact mem_erase.mpr ⟨hxv, hxS⟩
    · intro hu
      exact (mem_sdiff_closedNeighborhoodIn.mp (hJS hu)).2.2 hadj
  · rintro ⟨⟨hJS, hJ⟩, hu⟩
    refine ⟨?_, hJ⟩
    intro x hx
    obtain ⟨hxv, hxS⟩ := mem_erase.mp (hJS hx)
    refine mem_sdiff_closedNeighborhoodIn.mpr ⟨hxS, hxv, ?_⟩
    intro hvx
    exact hu ((hleaf x hxS hvx) ▸ hx)

/-- Elimination transports every observable, with its complete conditional law. -/
theorem heterogeneousNumerator_leaf (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u) (hden : 1 + activity v ≠ 0)
    (F : Finset V → ℝ) :
    FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity) F =
      (1 + activity v) * FiniteTilt.numerator (independentSubsets G (S.erase v))
        (heterogeneousWeight (leafReducedActivities activity v u))
        (leafConditionalMean (activity v / (1 + activity v)) v u F) := by
  classical
  rw [heterogeneousNumerator_delete_vertex G S activity F hv,
    independentSubsets_leaf_deleted G S hadj hleaf]
  simp only [FiniteTilt.numerator, sum_filter, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro J hJ
  rw [weight_leafReducedActivities activity v u hden J]
  unfold leafConditionalMean
  by_cases hu : u ∈ J
  · simp only [hu, if_pos, not_true_eq_false, if_false, mul_zero, add_zero]
    ring
  · simp only [hu, if_neg, not_false_eq_true, if_true, mul_one]
    field_simp
    ring

theorem heterogeneousPartition_leaf (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u) (hden : 1 + activity v ≠ 0) :
    heterogeneousPartition G S activity = (1 + activity v) *
      heterogeneousPartition G (S.erase v) (leafReducedActivities activity v u) := by
  have h := heterogeneousNumerator_leaf G S activity hv hadj hleaf hden (fun _ => 1)
  simpa [FiniteTilt.numerator, heterogeneousPartition, leafConditionalMean] using h

theorem heterogeneousMean_leaf (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u) (hden : 1 + activity v ≠ 0)
    (F : Finset V → ℝ) :
    heterogeneousMean G S activity F =
      heterogeneousMean G (S.erase v) (leafReducedActivities activity v u)
        (leafConditionalMean (activity v / (1 + activity v)) v u F) := by
  unfold heterogeneousMean FiniteTilt.mean
  rw [heterogeneousNumerator_leaf G S activity hv hadj hleaf hden F]
  change _ / heterogeneousPartition G S activity = _
  rw [heterogeneousPartition_leaf G S activity hv hadj hleaf hden]
  exact mul_div_mul_left _ _ hden


namespace FiniteTilt

theorem mean_congr {α : Type*} (s : Finset α) (w b a : α → ℝ)
    (h : ∀ x ∈ s, b x = a x) : mean s w b = mean s w a := by
  unfold mean numerator
  congr 1
  exact sum_congr rfl (fun x hx => congrArg (w x * ·) (h x hx))

theorem mean_add {α : Type*} (s : Finset α) (w b a : α → ℝ) :
    mean s w (fun x => b x + a x) = mean s w b + mean s w a := by
  simp only [mean, numerator, mul_add, sum_add_distrib, add_div]

theorem mean_sub {α : Type*} (s : Finset α) (w b a : α → ℝ) :
    mean s w (fun x => b x - a x) = mean s w b - mean s w a := by
  simp only [mean, numerator, mul_sub, sum_sub_distrib, sub_div]

theorem mean_const_mul {α : Type*} (s : Finset α) (w b : α → ℝ) (c : ℝ) :
    mean s w (fun x => c * b x) = c * mean s w b := by
  simp only [mean, numerator, mul_left_comm (w _) c, ← mul_sum, mul_div_assoc]

theorem mean_const {α : Type*} (s : Finset α) (w : α → ℝ) (c : ℝ)
    (hZ : total s w ≠ 0) : mean s w (fun _ => c) = c := by
  simp only [mean, numerator, ← sum_mul]
  change total s w * c / total s w = c
  exact mul_div_cancel_left₀ c hZ

theorem variance_eq_second_sub_mean_sq {α : Type*} (s : Finset α) (w b : α → ℝ) :
    variance s w b = mean s w (fun x => b x ^ 2) - mean s w b ^ 2 := by
  simp only [variance, covariance, pow_two]

theorem variance_add_const {α : Type*} (s : Finset α) (w b : α → ℝ) (c : ℝ)
    (hZ : total s w ≠ 0) :
    variance s w (fun x => c + b x) = variance s w b := by
  simp only [variance_eq_second_sub_mean_sq]
  have hs : (fun x => (c + b x) ^ 2) =
      (fun x => c ^ 2 + (2 * c) * b x + b x ^ 2) := by funext x; ring
  rw [hs]
  simp only [mean_add, mean_const_mul, mean_const s w _ hZ]
  ring

end FiniteTilt

theorem markedSum_leafReducedMarks (activity a : V → ℝ) (v u : V) (J : Finset V) :
    markedSum (leafReducedMarks activity a v u) J = markedSum a J -
      a v * (activity v / (1 + activity v)) * (if u ∈ J then 1 else 0) := by
  classical
  by_cases hu : u ∈ J
  · rw [if_pos hu]
    unfold markedSum leafReducedMarks
    rw [sum_update_of_mem hu]
    have hp : (∑ x ∈ J, a x) = a u + ∑ x ∈ J \ {u}, a x := by
      simpa only [Function.update_eq_self] using sum_update_of_mem hu a (a u)
    rw [hp]
    ring
  · simp only [if_neg hu, mul_zero, sub_zero, markedSum, leafReducedMarks,
      sum_update_of_notMem hu]

theorem leafConditionalMean_markedSum (activity a : V → ℝ) (v u : V) (J : Finset V)
    (hvJ : v ∉ J) :
    leafConditionalMean (activity v / (1 + activity v)) v u (markedSum a) J =
      a v * (activity v / (1 + activity v)) +
        markedSum (leafReducedMarks activity a v u) J := by
  classical
  rw [markedSum_leafReducedMarks]
  simp only [leafConditionalMean, markedSum, sum_insert hvJ]
  by_cases hu : u ∈ J <;> simp only [hu, if_true, if_false] <;> ring

theorem leafConditionalMean_markedSum_sq (activity a : V → ℝ) (v u : V) (J : Finset V)
    (hvJ : v ∉ J) :
    leafConditionalMean (activity v / (1 + activity v)) v u (fun K => markedSum a K ^ 2) J =
      (a v * (activity v / (1 + activity v)) + markedSum (leafReducedMarks activity a v u) J) ^ 2 +
        a v ^ 2 * (activity v / (1 + activity v)) * (1 - activity v / (1 + activity v)) *
          (1 - (if u ∈ J then 1 else 0)) := by
  classical
  rw [markedSum_leafReducedMarks]
  simp only [leafConditionalMean, markedSum, sum_insert hvJ]
  by_cases hu : u ∈ J <;> simp only [hu, if_true, if_false] <;> ring

/-- Exact source variance recursion. The mark is arbitrary and signed. -/
theorem heterogeneousVariance_leaf (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousVariance G S activity (markedSum a) =
      heterogeneousVariance G (S.erase v) (leafReducedActivities activity v u)
        (markedSum (leafReducedMarks activity a v u)) +
      a v ^ 2 * (activity v / (1 + activity v)) * (1 - activity v / (1 + activity v)) *
        (1 - heterogeneousMarginal G (S.erase v) (leafReducedActivities activity v u) u) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) (leafReducedActivities activity v u)
    (leafReducedActivities_nonneg activity S hv hactivity)
  have hZ : FiniteTilt.total (independentSubsets G (S.erase v))
      (heterogeneousWeight (leafReducedActivities activity v u)) ≠ 0 := ne_of_gt hpos
  have hnot (J) (hJ : J ∈ independentSubsets G (S.erase v)) : v ∉ J :=
    (mem_independentSubsets_erase_iff.mp hJ).2
  have hfirst := heterogeneousMean_leaf G S activity hv hadj hleaf hden (markedSum a)
  have hsecond := heterogeneousMean_leaf G S activity hv hadj hleaf hden (fun J => markedSum a J ^ 2)
  have hfirst' := FiniteTilt.mean_congr (independentSubsets G (S.erase v))
    (heterogeneousWeight (leafReducedActivities activity v u))
    (leafConditionalMean (activity v / (1 + activity v)) v u (markedSum a))
    (fun J => a v * (activity v / (1 + activity v)) + markedSum (leafReducedMarks activity a v u) J)
    (fun J hJ => leafConditionalMean_markedSum activity a v u J (hnot J hJ))
  have hsecond' := FiniteTilt.mean_congr (independentSubsets G (S.erase v))
    (heterogeneousWeight (leafReducedActivities activity v u))
    (leafConditionalMean (activity v / (1 + activity v)) v u (fun J => markedSum a J ^ 2))
    (fun J => (a v * (activity v / (1 + activity v)) + markedSum (leafReducedMarks activity a v u) J) ^ 2 +
        a v ^ 2 * (activity v / (1 + activity v)) * (1 - activity v / (1 + activity v)) *
          (1 - (if u ∈ J then 1 else 0)))
    (fun J hJ => leafConditionalMean_markedSum_sq activity a v u J (hnot J hJ))
  change heterogeneousMean G S activity (fun J => markedSum a J * markedSum a J) -
    heterogeneousMean G S activity (markedSum a) * heterogeneousMean G S activity (markedSum a) = _
  simp only [← pow_two]
  rw [hfirst, hsecond]
  simp only [heterogeneousMean] at hfirst' hsecond' ⊢
  rw [hfirst', hsecond']
  simp only [FiniteTilt.mean_add, FiniteTilt.mean_const_mul, FiniteTilt.mean_sub,
    FiniteTilt.mean_const _ _ _ hZ]
  have hshift := FiniteTilt.variance_add_const (independentSubsets G (S.erase v))
    (heterogeneousWeight (leafReducedActivities activity v u))
    (markedSum (leafReducedMarks activity a v u)) (a v * (activity v / (1 + activity v))) hZ
  simp only [FiniteTilt.variance_eq_second_sub_mean_sq, FiniteTilt.mean_add,
    FiniteTilt.mean_const _ _ _ hZ] at hshift
  change _ = FiniteTilt.variance _ _ _ + _ * (1 - FiniteTilt.mean _ _ _)
  rw [FiniteTilt.variance_eq_second_sub_mean_sq]
  linarith


/-- Every retained vertex has exactly its old occupation marginal. -/
theorem heterogeneousMarginal_leaf_retained (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v u x : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ y ∈ S, G.Adj v y → y = u) (hden : 1 + activity v ≠ 0) (hxv : x ≠ v) :
    heterogeneousMarginal G S activity x =
      heterogeneousMarginal G (S.erase v) (leafReducedActivities activity v u) x := by
  classical
  unfold heterogeneousMarginal
  rw [heterogeneousMean_leaf G S activity hv hadj hleaf hden]
  apply FiniteTilt.mean_congr
  intro J _
  simp only [leafConditionalMean, mem_insert, hxv, false_or]
  split_ifs <;> ring

/-- The removed leaf is Bernoulli only when its neighbor is unoccupied. -/
theorem heterogeneousMarginal_leaf_removed (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ y ∈ S, G.Adj v y → y = u)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousMarginal G S activity v = activity v / (1 + activity v) *
      (1 - heterogeneousMarginal G (S.erase v) (leafReducedActivities activity v u) u) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) (leafReducedActivities activity v u)
    (leafReducedActivities_nonneg activity S hv hactivity)
  have hZ : FiniteTilt.total (independentSubsets G (S.erase v))
      (heterogeneousWeight (leafReducedActivities activity v u)) ≠ 0 := ne_of_gt hpos
  unfold heterogeneousMarginal
  rw [heterogeneousMean_leaf G S activity hv hadj hleaf hden]
  have hc : heterogeneousMean G (S.erase v) (leafReducedActivities activity v u)
      (leafConditionalMean (activity v / (1 + activity v)) v u (fun J => if v ∈ J then 1 else 0)) =
      heterogeneousMean G (S.erase v) (leafReducedActivities activity v u)
        (fun J => activity v / (1 + activity v) * (1 - (if u ∈ J then 1 else 0))) := by
    apply FiniteTilt.mean_congr
    intro J hJ
    have hvJ := (mem_independentSubsets_erase_iff.mp hJ).2
    simp only [leafConditionalMean, hvJ, if_false, mem_insert_self, if_true]
    split_ifs <;> ring
  rw [hc]
  simp only [heterogeneousMean, FiniteTilt.mean_const_mul, FiniteTilt.mean_sub,
    FiniteTilt.mean_const _ _ _ hZ]

/-- The source term is expressed with the original graph's actual marginal. -/
theorem heterogeneousVariance_leaf_original_marginal (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousVariance G S activity (markedSum a) =
      heterogeneousVariance G (S.erase v) (leafReducedActivities activity v u)
        (markedSum (leafReducedMarks activity a v u)) +
      heterogeneousMarginal G S activity v * (1 - activity v / (1 + activity v)) * a v ^ 2 := by
  rw [heterogeneousVariance_leaf G S activity a hv hadj hleaf hactivity,
    heterogeneousMarginal_leaf_removed G S activity hv hadj hleaf hactivity]
  ring

theorem heterogeneousMean_isolated (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v : V} (hv : v ∈ S)
    (hiso : ∀ x ∈ S, ¬ G.Adj v x) (hden : 1 + activity v ≠ 0) (F : Finset V → ℝ) :
    heterogeneousMean G S activity F = heterogeneousMean G (S.erase v) activity
      (fun J => (1 - activity v / (1 + activity v)) * F J +
        (activity v / (1 + activity v)) * F (insert v J)) := by
  classical
  have hc : S \ closedNeighborhoodIn G S v = S.erase v := by
    ext x
    simp only [mem_sdiff_closedNeighborhoodIn, mem_erase]
    constructor
    · rintro ⟨hxS, hxv, _⟩; exact ⟨hxv, hxS⟩
    · rintro ⟨hxv, hxS⟩; exact ⟨hxS, hxv, hiso x hxS⟩
  have hnum := heterogeneousNumerator_delete_vertex G S activity F hv
  rw [hc] at hnum
  have hp := heterogeneousPartition_delete_vertex G S activity hv
  rw [hc] at hp
  have hp' : heterogeneousPartition G S activity =
      (1 + activity v) * heterogeneousPartition G (S.erase v) activity := by linarith
  have hnum' : FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity) F =
      (1 + activity v) * FiniteTilt.numerator (independentSubsets G (S.erase v))
        (heterogeneousWeight activity) (fun J => (1 - activity v / (1 + activity v)) * F J +
          (activity v / (1 + activity v)) * F (insert v J)) := by
    rw [hnum]
    simp only [FiniteTilt.numerator, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro J _
    field_simp
    ring
  unfold heterogeneousMean FiniteTilt.mean
  rw [hnum']
  change _ / heterogeneousPartition G S activity = _
  rw [hp']
  exact mul_div_mul_left _ _ hden

namespace FiniteTilt

theorem variance_of_conditional_moments {α β : Type*} (s : Finset α) (t : Finset β)
    (w b : α → ℝ) (w' b' : β → ℝ) (c noise : ℝ) (hZ : total t w' ≠ 0)
    (hfirst : mean s w b = mean t w' (fun x => c + b' x))
    (hsecond : mean s w (fun x => b x ^ 2) = mean t w' (fun x => (c + b' x) ^ 2) + noise) :
    variance s w b = variance t w' b' + noise := by
  rw [variance_eq_second_sub_mean_sq, hfirst, hsecond]
  have h := variance_add_const t w' b' c hZ
  rw [variance_eq_second_sub_mean_sq] at h
  linarith

end FiniteTilt

theorem heterogeneousVariance_isolated (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) {v : V} (hv : v ∈ S)
    (hiso : ∀ x ∈ S, ¬ G.Adj v x) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousVariance G S activity (markedSum a) =
      heterogeneousVariance G (S.erase v) activity (markedSum a) +
      a v ^ 2 * (activity v / (1 + activity v)) * (1 - activity v / (1 + activity v)) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) activity
    (fun x hx => hactivity x (mem_of_mem_erase hx))
  have hZ : FiniteTilt.total (independentSubsets G (S.erase v)) (heterogeneousWeight activity) ≠ 0 :=
    ne_of_gt hpos
  have hnot (J) (hJ : J ∈ independentSubsets G (S.erase v)) : v ∉ J :=
    (mem_independentSubsets_erase_iff.mp hJ).2
  apply FiniteTilt.variance_of_conditional_moments _ _ _ _ _ _
    (a v * (activity v / (1 + activity v))) _ hZ
  · change heterogeneousMean G S activity _ = heterogeneousMean G (S.erase v) activity _
    rw [heterogeneousMean_isolated G S activity hv hiso hden]
    apply FiniteTilt.mean_congr
    intro J hJ
    simp only [markedSum, sum_insert (hnot J hJ)]
    ring
  · change heterogeneousMean G S activity _ = heterogeneousMean G (S.erase v) activity _ + _
    rw [heterogeneousMean_isolated G S activity hv hiso hden]
    have heq : heterogeneousMean G (S.erase v) activity
        (fun J => (1 - activity v / (1 + activity v)) * markedSum a J ^ 2 +
          activity v / (1 + activity v) * markedSum a (insert v J) ^ 2) =
        heterogeneousMean G (S.erase v) activity
          (fun J => (a v * (activity v / (1 + activity v)) + markedSum a J) ^ 2 +
            a v ^ 2 * (activity v / (1 + activity v)) * (1 - activity v / (1 + activity v))) := by
      apply FiniteTilt.mean_congr
      intro J hJ
      simp only [markedSum, sum_insert (hnot J hJ)]
      ring
    rw [heq]
    exact (FiniteTilt.mean_add _ _ _ _).trans (by rw [FiniteTilt.mean_const _ _ _ hZ]; rfl)

#print axioms heterogeneousMean_leaf
#print axioms heterogeneousVariance_leaf_original_marginal
#print axioms heterogeneousMarginal_leaf_retained
#print axioms heterogeneousVariance_isolated
end ForestUnimodality

