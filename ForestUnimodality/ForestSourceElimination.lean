import ForestUnimodality.ForestSourceLeaf
import ForestUnimodality.EdgeDeletion

/-! A genuine forest source response decomposition obtained by leaf elimination.
The transcript records the effective occupation probability and signed response
at each elimination. Its constructors require the exact graph, activities and
marks at every step; existence is proved for every finite induced forest. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

/-- A leaf-elimination transcript: `(vertex, effective probability, response)`.
Responses and activities are updated at the unique retained neighbor. -/
inductive SourceElimination (G : SimpleGraph V) :
    Finset V → (V → ℝ) → (V → ℝ) → List (V × ℝ × ℝ) → Prop
  | nil (activity a : V → ℝ) : SourceElimination G ∅ activity a []
  | isolated {S : Finset V} {activity a : V → ℝ} {v : V} {rest : List (V × ℝ × ℝ)}
      (hv : v ∈ S) (hiso : ∀ x ∈ S, ¬ G.Adj v x)
      (tail : SourceElimination G (S.erase v) activity a rest) :
      SourceElimination G S activity a ((v, activity v / (1 + activity v), a v) :: rest)
  | leaf {S : Finset V} {activity a : V → ℝ} {v u : V} {rest : List (V × ℝ × ℝ)}
      (hv : v ∈ S) (hu : u ∈ S) (hadj : G.Adj v u)
      (hleaf : ∀ x ∈ S, G.Adj v x → x = u)
      (tail : SourceElimination G (S.erase v) (leafReducedActivities activity v u)
        (leafReducedMarks activity a v u) rest) :
      SourceElimination G S activity a ((v, activity v / (1 + activity v), a v) :: rest)

/-- Forest structure supplies the transcript; no response data is assumed. -/
theorem exists_sourceElimination (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (activity a : V → ℝ) : ∃ trace, SourceElimination G S activity a trace := by
  classical
  induction S using Finset.strongInductionOn generalizing activity a with
  | _ S ih =>
    by_cases hS : S = ∅
    · subst S; exact ⟨[], SourceElimination.nil activity a⟩
    obtain ⟨v, hv, hsmall⟩ := exists_closedNeighborhoodIn_card_le_two G hG S (nonempty_iff_ne_empty.mpr hS)
    have hdegree : (S.filter (G.Adj v)).card ≤ 1 := by
      rw [card_closedNeighborhoodIn_eq_degree_add_one G S hv] at hsmall
      omega
    by_cases he : ∃ u ∈ S, G.Adj v u
    · obtain ⟨u, hu, hadj⟩ := he
      have hleaf : ∀ x ∈ S, G.Adj v x → x = u := by
        intro x hx hadjx
        exact card_le_one.mp hdegree x (mem_filter.mpr ⟨hx, hadjx⟩) u (mem_filter.mpr ⟨hu, hadj⟩)
      obtain ⟨rest, hr⟩ := ih (S.erase v) (erase_ssubset hv)
        (leafReducedActivities activity v u) (leafReducedMarks activity a v u)
      exact ⟨_, SourceElimination.leaf hv hu hadj hleaf hr⟩
    · have hiso : ∀ x ∈ S, ¬ G.Adj v x := by simpa only [not_exists, not_and] using he
      obtain ⟨rest, hr⟩ := ih (S.erase v) (erase_ssubset hv) activity a
      exact ⟨_, SourceElimination.isolated hv hiso hr⟩

theorem SourceElimination.vertices {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace) :
    (trace.map Prod.fst).toFinset = S := by
  classical
  induction h with
  | nil => simp
  | isolated hv _ _ ih => simp only [List.map_cons, List.toFinset_cons, ih, insert_erase hv]
  | leaf hv _ _ _ _ ih => simp only [List.map_cons, List.toFinset_cons, ih, insert_erase hv]

theorem SourceElimination.mem {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)}
    (h : SourceElimination G S activity a trace) {r : V × ℝ × ℝ} (hr : r ∈ trace) : r.1 ∈ S := by
  rw [← h.vertices]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)

theorem SourceElimination.nodup {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace) :
    (trace.map Prod.fst).Nodup := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hm
    have hmem := tail.mem hr
    rw [heq] at hmem
    exact (mem_erase.mp hmem).1 rfl
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hm
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hm
    have hmem := tail.mem hr
    rw [heq] at hmem
    exact (mem_erase.mp hmem).1 rfl

theorem SourceElimination.probability_bounds {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) : ∀ r ∈ trace, 0 ≤ r.2.1 ∧ r.2.1 < 1 := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hv0 := hactivity _ hv
      have hd : 0 < 1 + activity v := by linarith
      exact ⟨div_nonneg hv0 hd.le, (div_lt_one hd).mpr (by linarith)⟩
    · exact ih (fun x hx => hactivity x (mem_of_mem_erase hx)) r hr
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · have hv0 := hactivity _ hv
      have hd : 0 < 1 + activity v := by linarith
      exact ⟨div_nonneg hv0 hd.le, (div_lt_one hd).mpr (by linarith)⟩
    · exact ih (leafReducedActivities_nonneg _ _ hv hactivity) r hr

theorem heterogeneousMarginal_isolated_retained (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v x : V} (hv : v ∈ S)
    (hiso : ∀ y ∈ S, ¬ G.Adj v y) (hden : 1 + activity v ≠ 0) (hxv : x ≠ v) :
    heterogeneousMarginal G S activity x = heterogeneousMarginal G (S.erase v) activity x := by
  classical
  unfold heterogeneousMarginal
  rw [heterogeneousMean_isolated G S activity hv hiso hden]
  apply FiniteTilt.mean_congr
  intro J _
  simp only [mem_insert, hxv, false_or]
  ring

theorem heterogeneousMarginal_isolated_removed (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v : V} (hv : v ∈ S)
    (hiso : ∀ y ∈ S, ¬ G.Adj v y) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousMarginal G S activity v = activity v / (1 + activity v) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) activity
    (fun x hx => hactivity x (mem_of_mem_erase hx))
  unfold heterogeneousMarginal
  rw [heterogeneousMean_isolated G S activity hv hiso hden]
  have hc : heterogeneousMean G (S.erase v) activity
      (fun J => (1 - activity v / (1 + activity v)) * (if v ∈ J then 1 else 0) +
        activity v / (1 + activity v) * (if v ∈ insert v J then 1 else 0)) =
      heterogeneousMean G (S.erase v) activity (fun _ => activity v / (1 + activity v)) := by
    apply FiniteTilt.mean_congr
    intro J hJ
    simp [(mem_independentSubsets_erase_iff.mp hJ).2]
  rw [hc]
  exact FiniteTilt.mean_const _ _ _ (ne_of_gt hpos)

/-- The response sum uses the occupation marginals of the original graph. -/
noncomputable def sourceVarianceSum (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (trace : List (V × ℝ × ℝ)) : ℝ :=
  (trace.map fun r => heterogeneousMarginal G S activity r.1 * (1 - r.2.1) * r.2.2 ^ 2).sum

theorem SourceElimination.variance_identity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousVariance G S activity (markedSum a) = sourceVarianceSum G S activity trace := by
  classical
  induction h with
  | nil =>
    have he : independentSubsets G ∅ = {∅} := by
      ext J
      simp only [mem_independentSubsets, subset_empty, mem_singleton]
      constructor
      · exact And.left
      · rintro rfl
        exact ⟨rfl, by simp [SimpleGraph.IsIndepSet]⟩
    simp [heterogeneousVariance, FiniteTilt.variance, FiniteTilt.covariance, FiniteTilt.mean,
      FiniteTilt.numerator, FiniteTilt.total, he, markedSum, sourceVarianceSum]
  | @isolated S activity a v rest hv hiso tail ih =>
    have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
    have ht : sourceVarianceSum G (S.erase v) activity rest = sourceVarianceSum G S activity rest := by
      unfold sourceVarianceSum
      congr 1
      apply List.map_congr_left
      intro r hr
      rw [heterogeneousMarginal_isolated_retained G S activity hv hiso hden (mem_erase.mp (tail.mem hr)).1]
    rw [heterogeneousVariance_isolated G S activity a hv hiso hactivity,
      ih (fun x hx => hactivity x (mem_of_mem_erase hx)), ht]
    simp only [sourceVarianceSum, List.map_cons, List.sum_cons]
    rw [heterogeneousMarginal_isolated_removed G S activity hv hiso hactivity]
    ring
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
    have ht : sourceVarianceSum G (S.erase v) (leafReducedActivities activity v u) rest =
        sourceVarianceSum G S activity rest := by
      unfold sourceVarianceSum
      congr 1
      apply List.map_congr_left
      intro r hr
      rw [heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf hden (mem_erase.mp (tail.mem hr)).1]
    rw [heterogeneousVariance_leaf_original_marginal G S activity a hv hadj hleaf hactivity,
      ih (leafReducedActivities_nonneg _ _ hv hactivity), ht]
    simp only [sourceVarianceSum, List.map_cons, List.sum_cons]
    ring

/-- Complete genuine response decomposition for every finite forest. The
transcript includes the exact recursive mark/activity updates. -/
theorem exists_forest_source_variance_decomposition (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (activity a : V → ℝ) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∃ trace, SourceElimination G S activity a trace ∧
      (trace.map Prod.fst).toFinset = S ∧ (trace.map Prod.fst).Nodup ∧
      (∀ r ∈ trace, 0 ≤ r.2.1 ∧ r.2.1 < 1) ∧
      heterogeneousVariance G S activity (markedSum a) = sourceVarianceSum G S activity trace := by
  obtain ⟨trace, h⟩ := exists_sourceElimination G hG S activity a
  exact ⟨trace, h, h.vertices, h.nodup, h.probability_bounds hactivity, h.variance_identity hactivity⟩


theorem heterogeneousMarkedMean_leaf (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) {v u : V} (hv : v ∈ S) (hadj : G.Adj v u)
    (hleaf : ∀ x ∈ S, G.Adj v x → x = u) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousMean G S activity (markedSum a) = a v * (activity v / (1 + activity v)) +
      heterogeneousMean G (S.erase v) (leafReducedActivities activity v u)
        (markedSum (leafReducedMarks activity a v u)) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) (leafReducedActivities activity v u)
    (leafReducedActivities_nonneg activity S hv hactivity)
  rw [heterogeneousMean_leaf G S activity hv hadj hleaf hden]
  have he := FiniteTilt.mean_congr (independentSubsets G (S.erase v))
    (heterogeneousWeight (leafReducedActivities activity v u))
    (leafConditionalMean (activity v / (1 + activity v)) v u (markedSum a))
    (fun J => a v * (activity v / (1 + activity v)) + markedSum (leafReducedMarks activity a v u) J)
    (fun J hJ => leafConditionalMean_markedSum activity a v u J (mem_independentSubsets_erase_iff.mp hJ).2)
  change FiniteTilt.mean _ _ _ = _
  rw [he, FiniteTilt.mean_add, FiniteTilt.mean_const _ _ _ (ne_of_gt hpos)]
  rfl

theorem heterogeneousMarkedMean_isolated (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) {v : V} (hv : v ∈ S)
    (hiso : ∀ x ∈ S, ¬ G.Adj v x) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousMean G S activity (markedSum a) = a v * (activity v / (1 + activity v)) +
      heterogeneousMean G (S.erase v) activity (markedSum a) := by
  classical
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have hpos := heterogeneousPartition_pos G (S.erase v) activity
    (fun x hx => hactivity x (mem_of_mem_erase hx))
  rw [heterogeneousMean_isolated G S activity hv hiso hden]
  have he : heterogeneousMean G (S.erase v) activity
      (fun J => (1 - activity v / (1 + activity v)) * markedSum a J +
        activity v / (1 + activity v) * markedSum a (insert v J)) =
      heterogeneousMean G (S.erase v) activity
        (fun J => a v * (activity v / (1 + activity v)) + markedSum a J) := by
    apply FiniteTilt.mean_congr
    intro J hJ
    simp only [markedSum, sum_insert (mem_independentSubsets_erase_iff.mp hJ).2]
    ring
  rw [he]
  exact (FiniteTilt.mean_add _ _ _ _).trans (by rw [FiniteTilt.mean_const _ _ _ (ne_of_gt hpos)]; rfl)

/-- The signed mean identity is the source response telescoping identity. -/
theorem SourceElimination.mean_identity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousMean G S activity (markedSum a) = (trace.map fun r => r.2.1 * r.2.2).sum := by
  classical
  induction h with
  | nil =>
    have he : independentSubsets G ∅ = {∅} := by
      ext J
      simp only [mem_independentSubsets, subset_empty, mem_singleton]
      constructor
      · exact And.left
      · rintro rfl
        exact ⟨rfl, by simp [SimpleGraph.IsIndepSet]⟩
    simp [heterogeneousMean, FiniteTilt.mean, FiniteTilt.numerator, he, markedSum]
  | @isolated S activity a v rest hv hiso tail ih =>
    rw [heterogeneousMarkedMean_isolated G S activity a hv hiso hactivity,
      ih (fun x hx => hactivity x (mem_of_mem_erase hx))]
    simp only [List.map_cons, List.sum_cons]
    ring
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    rw [heterogeneousMarkedMean_leaf G S activity a hv hadj hleaf hactivity,
      ih (leafReducedActivities_nonneg _ _ hv hactivity)]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- Effective subtree occupancy dominates the original occupation marginal. -/
theorem SourceElimination.marginal_le_probability {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∀ r ∈ trace, heterogeneousMarginal G S activity r.1 ≤ r.2.1 := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (heterogeneousMarginal_isolated_removed G S activity hv hiso hactivity).le
    · rw [heterogeneousMarginal_isolated_retained G S activity hv hiso
        (ne_of_gt (by linarith [hactivity v hv])) (mem_erase.mp (tail.mem hr)).1]
      exact ih (fun x hx => hactivity x (mem_of_mem_erase hx)) r hr
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    intro r hr
    have hnonneg := leafReducedActivities_nonneg activity S (u := u) hv hactivity
    rcases List.mem_cons.mp hr with rfl | hr
    · change heterogeneousMarginal G S activity v ≤ activity v / (1 + activity v)
      rw [heterogeneousMarginal_leaf_removed G S activity hv hadj hleaf hactivity]
      have hm := (heterogeneousMarginal_mem_Icc G (S.erase v)
        (leafReducedActivities activity v u) hnonneg u).1
      have hp : 0 ≤ activity v / (1 + activity v) := div_nonneg (hactivity v hv) (by linarith [hactivity v hv])
      nlinarith
    · rw [heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf
        (ne_of_gt (by linarith [hactivity v hv])) (mem_erase.mp (tail.mem hr)).1]
      exact ih hnonneg r hr

/-- A source response bound for the actual forest distribution. The responses
are the recursively updated `d` values, not the original marks `a`. -/
theorem SourceElimination.variance_le_quarter_response_sq {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    heterogeneousVariance G S activity (markedSum a) ≤
      (1 / 4 : ℝ) * (trace.map fun r => r.2.2 ^ 2).sum := by
  rw [h.variance_identity hactivity, sourceVarianceSum, ← List.sum_map_mul_left]
  apply List.sum_le_sum
  intro r hr
  have hp := h.probability_bounds hactivity r hr
  have hm := h.marginal_le_probability hactivity r hr
  have hpn : 0 ≤ 1 - r.2.1 := by linarith
  have hfirst := mul_le_mul_of_nonneg_right hm hpn
  have hquart : r.2.1 * (1 - r.2.1) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (r.2.1 - 1 / 2)]
  exact mul_le_mul_of_nonneg_right (hfirst.trans hquart) (sq_nonneg _)


theorem leafReducedActivities_le (activity : V → ℝ) (S : Finset V) {v u : V}
    (hv : v ∈ S) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∀ x ∈ S.erase v, leafReducedActivities activity v u x ≤ activity x := by
  intro x hx
  by_cases hxu : x = u
  · subst x
    simp only [leafReducedActivities, Function.update_self]
    exact div_le_self (hactivity u (mem_of_mem_erase hx)) (by linarith [hactivity v hv])
  · simp only [leafReducedActivities, Function.update_of_ne hxu, le_refl]

/-- Elimination only lowers an effective activity. Thus every recorded
probability is bounded by the original vertex's own activity. -/
theorem SourceElimination.probability_le_activity {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∀ r ∈ trace, r.2.1 ≤ activity r.1 / (1 + activity r.1) := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact ih (fun x hx => hactivity x (mem_of_mem_erase hx)) r hr
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · have hnn := leafReducedActivities_nonneg activity S (u := u) hv hactivity
      apply (ih hnn r hr).trans
      have hrS := tail.mem hr
      have h0 := hnn _ hrS
      have h1 := hactivity _ (mem_of_mem_erase hrS)
      have hle := leafReducedActivities_le activity S (u := u) hv hactivity _ hrS
      apply (div_le_div_iff₀ (by linarith : 0 < 1 + leafReducedActivities activity v u r.1)
        (by linarith : 0 < 1 + activity r.1)).mpr
      nlinarith

theorem SourceElimination.probability_pos {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 < activity x) : ∀ r ∈ trace, 0 < r.2.1 := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact div_pos (hactivity v hv) (by linarith [hactivity v hv])
    · exact ih (fun x hx => hactivity x (mem_of_mem_erase hx)) r hr
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact div_pos (hactivity v hv) (by linarith [hactivity v hv])
    · apply ih ?_ r hr
      intro x hx
      by_cases hxu : x = u
      · subst x
        simp only [leafReducedActivities, Function.update_self]
        exact div_pos (hactivity u (mem_of_mem_erase hx)) (by linarith [hactivity v hv])
      · simpa only [leafReducedActivities, Function.update_of_ne hxu] using
          hactivity x (mem_of_mem_erase hx)

/-- The full real probability domain needed by bounded-activity source rows. -/
theorem SourceElimination.probability_interval {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    {b : ℝ} (hactivity : ∀ x ∈ S, 0 < activity x ∧ activity x ≤ b) :
    ∀ r ∈ trace, 0 < r.2.1 ∧ r.2.1 ≤ b / (1 + b) := by
  intro r hr
  have hb := hactivity _ (h.mem hr)
  refine ⟨h.probability_pos (fun x hx => (hactivity x hx).1) r hr, ?_⟩
  apply (h.probability_le_activity (fun x hx => (hactivity x hx).1.le) r hr).trans
  apply (div_le_div_iff₀ (by linarith : 0 < 1 + activity r.1) (by linarith : 0 < 1 + b)).mpr
  nlinarith

#print axioms exists_sourceElimination
#print axioms SourceElimination.variance_identity
#print axioms SourceElimination.mean_identity
#print axioms SourceElimination.variance_le_quarter_response_sq
#print axioms SourceElimination.probability_interval
#print axioms exists_forest_source_variance_decomposition
end ForestUnimodality
