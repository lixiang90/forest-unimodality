import ForestUnimodality.ForestSourceElimination

/-! Parent/child message equations extracted from the actual heterogeneous
forest elimination transcript. All messages remain tied to the same genuine
finite independent-set distribution. -/

namespace ForestUnimodality
open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def sourceChildren (S : Finset V) (parent : V → Option V) (x : V) : Finset V :=
  S.filter (fun y => parent y = some x)

noncomputable def sourceChildProduct (S : Finset V) (parent : V → Option V) (p : V → ℝ) (x : V) : ℝ :=
  ∏ y ∈ sourceChildren S parent x, (1 - p y)

noncomputable def sourceChildResponse (S : Finset V) (parent : V → Option V)
    (p d : V → ℝ) (x : V) : ℝ := ∑ y ∈ sourceChildren S parent x, p y * d y

noncomputable def sourceParentMass (G : SimpleGraph V) (S : Finset V) (activity : V → ℝ) (o : Option V) : ℝ :=
  match o with
  | none => 0
  | some y => heterogeneousMarginal G S activity y

/-- The local equations use an actual parent function and actual graph marginals.
The odds relation is written without division to include zero activities. -/
structure SourceMessages (G : SimpleGraph V) (S : Finset V) (activity a : V → ℝ)
    (parent : V → Option V) (p d : V → ℝ) : Prop where
  parent_mem : ∀ x ∈ S, ∀ y, parent x = some y → y ∈ S ∧ G.Adj x y
  probability : ∀ x ∈ S, 0 ≤ p x ∧ p x < 1
  odds : ∀ x ∈ S, p x = (1 - p x) * activity x * sourceChildProduct S parent p x
  response : ∀ x ∈ S, d x = a x - sourceChildResponse S parent p d x
  marginal : ∀ x ∈ S, heterogeneousMarginal G S activity x =
    p x * (1 - sourceParentMass G S activity (parent x))

noncomputable def sourceReducedActivity (activity : V → ℝ) (v : V) (o : Option V) (x : V) : ℝ :=
  if o = some x then activity x / (1 + activity v) else activity x

noncomputable def sourceReducedMark (activity a : V → ℝ) (v : V) (o : Option V) (x : V) : ℝ :=
  if o = some x then a x - a v * (activity v / (1 + activity v)) else a x

theorem sourceChildren_extend (S : Finset V) (parent : V → Option V) {v : V} (hv : v ∈ S)
    (o : Option V) (x : V) :
    sourceChildren S (Function.update parent v o) x =
      if o = some x then insert v (sourceChildren (S.erase v) parent x)
        else sourceChildren (S.erase v) parent x := by
  classical
  by_cases hox : o = some x <;> ext y <;> by_cases hyv : y = v <;> simp_all [sourceChildren]
theorem sourceChildProduct_extend (S : Finset V) (parent : V → Option V)
    (p : V → ℝ) {v : V} (hv : v ∈ S) (o : Option V) (q : ℝ) (x : V) :
    sourceChildProduct S (Function.update parent v o) (Function.update p v q) x =
      if o = some x then (1 - q) * sourceChildProduct (S.erase v) parent p x
        else sourceChildProduct (S.erase v) parent p x := by
  classical
  have hvnot : v ∉ sourceChildren (S.erase v) parent x := by simp [sourceChildren]
  have he : (∏ y ∈ sourceChildren (S.erase v) parent x, (1 - Function.update p v q y)) =
      sourceChildProduct (S.erase v) parent p x := by
    apply prod_congr rfl
    intro y hy
    rw [Function.update_of_ne (mem_erase.mp (mem_filter.mp hy).1).1]
  unfold sourceChildProduct
  rw [sourceChildren_extend S parent hv o x]
  split_ifs
  · rw [prod_insert hvnot, Function.update_self, he]
    rfl
  · exact he

theorem sourceChildResponse_extend (S : Finset V) (parent : V → Option V)
    (p d : V → ℝ) {v : V} (hv : v ∈ S) (o : Option V) (q b : ℝ) (x : V) :
    sourceChildResponse S (Function.update parent v o) (Function.update p v q) (Function.update d v b) x =
      if o = some x then q * b + sourceChildResponse (S.erase v) parent p d x
        else sourceChildResponse (S.erase v) parent p d x := by
  classical
  have hvnot : v ∉ sourceChildren (S.erase v) parent x := by simp [sourceChildren]
  have he : (∑ y ∈ sourceChildren (S.erase v) parent x, Function.update p v q y * Function.update d v b y) =
      sourceChildResponse (S.erase v) parent p d x := by
    apply sum_congr rfl
    intro y hy
    rw [Function.update_of_ne (mem_erase.mp (mem_filter.mp hy).1).1,
      Function.update_of_ne (mem_erase.mp (mem_filter.mp hy).1).1]
  unfold sourceChildResponse
  rw [sourceChildren_extend S parent hv o x]
  split_ifs
  · rw [sum_insert hvnot, Function.update_self, Function.update_self, he]
    rfl
  · exact he

theorem SourceMessages.children_eq_empty_of_not_mem {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {x : V} (hx : x ∉ S) :
    sourceChildren S parent x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hyS, hpar⟩ := mem_filter.mp hy
  exact hx (h.parent_mem y hyS x hpar).1

/-- Adding the first removed vertex reconstructs every local message equation.
The transport hypotheses are supplied below by the proved actual leaf laws. -/
theorem SourceMessages.extend {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} {v : V} (hv : v ∈ S) (o : Option V)
    (ho : ∀ y, o = some y → y ∈ S.erase v ∧ G.Adj v y)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x)
    (h : SourceMessages G (S.erase v) (sourceReducedActivity activity v o)
      (sourceReducedMark activity a v o) parent p d)
    (hretain : ∀ x ∈ S.erase v, heterogeneousMarginal G S activity x =
      heterogeneousMarginal G (S.erase v) (sourceReducedActivity activity v o) x)
    (hremove : heterogeneousMarginal G S activity v = activity v / (1 + activity v) *
      (1 - sourceParentMass G S activity o)) :
    SourceMessages G S activity a (Function.update parent v o)
      (Function.update p v (activity v / (1 + activity v))) (Function.update d v (a v)) := by
  classical
  let q := activity v / (1 + activity v)
  have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
  have honv : o ≠ some v := fun he => (mem_erase.mp (ho v he).1).1 rfl
  have hempty := h.children_eq_empty_of_not_mem (Finset.notMem_erase v S)
  have hcp : sourceChildProduct (S.erase v) parent p v = 1 := by simp [sourceChildProduct, hempty]
  have hcr : sourceChildResponse (S.erase v) parent p d v = 0 := by simp [sourceChildResponse, hempty]
  constructor
  · intro x hx y hy
    by_cases hxv : x = v
    · subst x
      rw [Function.update_self] at hy
      exact ⟨mem_of_mem_erase (ho y hy).1, (ho y hy).2⟩
    · rw [Function.update_of_ne hxv] at hy
      obtain ⟨hyS, hadj⟩ := h.parent_mem x (mem_erase.mpr ⟨hxv, hx⟩) y hy
      exact ⟨mem_of_mem_erase hyS, hadj⟩
  · intro x hx
    by_cases hxv : x = v
    · subst x
      rw [Function.update_self]
      exact ⟨div_nonneg (hactivity v hv) (by linarith [hactivity v hv]),
        (div_lt_one (by linarith [hactivity v hv])).mpr (by linarith)⟩
    · rw [Function.update_of_ne hxv]
      exact h.probability x (mem_erase.mpr ⟨hxv, hx⟩)
  · intro x hx
    rw [sourceChildProduct_extend S parent p hv o _ x]
    by_cases hxv : x = v
    · subst x
      rw [Function.update_self, if_neg honv, hcp]
      field_simp
      ring
    · rw [Function.update_of_ne hxv]
      have hold := h.odds x (mem_erase.mpr ⟨hxv, hx⟩)
      by_cases hox : o = some x
      · rw [if_pos hox]
        have he : sourceReducedActivity activity v o x =
            activity x * (1 - activity v / (1 + activity v)) := by
          rw [sourceReducedActivity, if_pos hox]
          field_simp
          ring
        rw [he] at hold
        nlinarith [hold]
      · rw [if_neg hox]
        simpa only [sourceReducedActivity, if_neg hox] using hold
  · intro x hx
    rw [sourceChildResponse_extend S parent p d hv o _ _ x]
    by_cases hxv : x = v
    · subst x
      rw [Function.update_self, if_neg honv, hcr, sub_zero]
    · rw [Function.update_of_ne hxv]
      have hold := h.response x (mem_erase.mpr ⟨hxv, hx⟩)
      by_cases hox : o = some x
      · rw [if_pos hox]
        simp only [sourceReducedMark, if_pos hox] at hold
        linarith
      · rw [if_neg hox]
        simpa only [sourceReducedMark, if_neg hox] using hold
  · intro x hx
    by_cases hxv : x = v
    · subst x
      simpa only [Function.update_self] using hremove
    · rw [Function.update_of_ne hxv, Function.update_of_ne hxv, hretain x (mem_erase.mpr ⟨hxv, hx⟩),
        h.marginal x (mem_erase.mpr ⟨hxv, hx⟩)]
      congr 2
      cases hp : parent x with
      | none => rfl
      | some y =>
        exact (hretain y (h.parent_mem x (mem_erase.mpr ⟨hxv, hx⟩) y hp).1).symm


@[simp] theorem sourceReducedActivity_none (activity : V → ℝ) (v : V) :
    sourceReducedActivity activity v none = activity := by funext x; simp [sourceReducedActivity]

@[simp] theorem sourceReducedMark_none (activity a : V → ℝ) (v : V) :
    sourceReducedMark activity a v none = a := by funext x; simp [sourceReducedMark]

theorem sourceReducedActivity_some (activity : V → ℝ) (v u : V) :
    sourceReducedActivity activity v (some u) = leafReducedActivities activity v u := by
  funext x
  by_cases hxu : x = u
  · subst x; simp [sourceReducedActivity, leafReducedActivities]
  · simp [sourceReducedActivity, leafReducedActivities, hxu, Ne.symm hxu]

theorem sourceReducedMark_some (activity a : V → ℝ) (v u : V) :
    sourceReducedMark activity a v (some u) = leafReducedMarks activity a v u := by
  funext x
  by_cases hxu : x = u
  · subst x; simp [sourceReducedMark, leafReducedMarks]
  · simp [sourceReducedMark, leafReducedMarks, hxu, Ne.symm hxu]
/-- Complete extraction from the genuine graph elimination transcript. -/
theorem SourceElimination.messages {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∃ parent p d, SourceMessages G S activity a parent p d ∧
      ∀ r ∈ trace, p r.1 = r.2.1 ∧ d r.1 = r.2.2 := by
  classical
  induction h with
  | nil =>
    refine ⟨fun _ => none, fun _ => 0, fun _ => 0, ?_, ?_⟩
    · constructor <;> simp
    · simp
  | @isolated S activity a v rest hv hiso tail ih =>
    obtain ⟨parent, p, d, hm, hagree⟩ := ih (fun x hx => hactivity x (mem_of_mem_erase hx))
    have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
    refine ⟨Function.update parent v none, Function.update p v (activity v / (1 + activity v)),
      Function.update d v (a v), ?_, ?_⟩
    · apply SourceMessages.extend hv none (by simp) hactivity
      · simpa only [sourceReducedActivity_none, sourceReducedMark_none] using hm
      · intro x hx
        simpa only [sourceReducedActivity_none] using
          heterogeneousMarginal_isolated_retained G S activity hv hiso hden (mem_erase.mp hx).1
      · simpa only [sourceParentMass, sub_zero, mul_one] using
          heterogeneousMarginal_isolated_removed G S activity hv hiso hactivity
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only [Function.update_self, and_self]
      · simpa only [Function.update_of_ne (mem_erase.mp (tail.mem hr)).1] using hagree r hr
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    obtain ⟨parent, p, d, hm, hagree⟩ := ih (leafReducedActivities_nonneg activity S hv hactivity)
    have hden : 1 + activity v ≠ 0 := ne_of_gt (by linarith [hactivity v hv])
    refine ⟨Function.update parent v (some u), Function.update p v (activity v / (1 + activity v)),
      Function.update d v (a v), ?_, ?_⟩
    · refine SourceMessages.extend hv (some u) ?_ hactivity ?_ ?_ ?_
      · intro y hy
        have he : u = y := Option.some.inj hy
        subst y
        exact ⟨mem_erase.mpr ⟨hadj.ne.symm, hu⟩, hadj⟩
      · rw [sourceReducedActivity_some, sourceReducedMark_some]
        exact hm
      · intro x hx
        rw [sourceReducedActivity_some]
        exact heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf hden (mem_erase.mp hx).1
      · rw [sourceParentMass, heterogeneousMarginal_leaf_removed G S activity hv hadj hleaf hactivity,
          heterogeneousMarginal_leaf_retained G S activity hv hadj hleaf hden hadj.ne.symm]
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only [Function.update_self, and_self]
      · simpa only [Function.update_of_ne (mem_erase.mp (tail.mem hr)).1] using hagree r hr

theorem SourceMessages.odds_eq {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    {x : V} (hx : x ∈ S) :
    p x / (1 - p x) = activity x * sourceChildProduct S parent p x := by
  apply (div_eq_iff (ne_of_gt (sub_pos.mpr (h.probability x hx).2))).mpr
  have he := h.odds x hx
  nlinarith [he]

/-- Every finite forest admits parent/child messages with the exact three
local equations. Existence invokes the proved true-distribution transcript. -/
theorem exists_forest_source_messages (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity a : V → ℝ) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∃ parent p d, SourceMessages G S activity a parent p d := by
  obtain ⟨trace, ht⟩ := exists_sourceElimination G hG S activity a
  obtain ⟨parent, p, d, hm, _⟩ := ht.messages hactivity
  exact ⟨parent, p, d, hm⟩


theorem SourceElimination.sum_vertices {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {trace : List (V × ℝ × ℝ)} (h : SourceElimination G S activity a trace)
    (f : V → ℝ) : (trace.map fun r => f r.1).sum = ∑ x ∈ S, f x := by
  induction h with
  | nil => simp
  | @isolated S activity a v rest hv hiso tail ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (add_comm _ _).trans (sum_erase_add S f hv)
  | @leaf S activity a v u rest hv hu hadj hleaf tail ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (add_comm _ _).trans (sum_erase_add S f hv)

/-- Extraction together with global first and second source moments. -/
theorem exists_forest_source_messages_moments (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    (activity a : V → ℝ) (hactivity : ∀ x ∈ S, 0 ≤ activity x) :
    ∃ parent p d, SourceMessages G S activity a parent p d ∧
      heterogeneousMean G S activity (markedSum a) = ∑ x ∈ S, p x * d x ∧
      heterogeneousVariance G S activity (markedSum a) =
        ∑ x ∈ S, heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2 := by
  obtain ⟨trace, ht⟩ := exists_sourceElimination G hG S activity a
  obtain ⟨parent, p, d, hm, hagree⟩ := ht.messages hactivity
  refine ⟨parent, p, d, hm, ?_, ?_⟩
  · rw [ht.mean_identity hactivity, ← ht.sum_vertices (fun x => p x * d x)]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [(hagree r hr).1, (hagree r hr).2]
  · rw [ht.variance_identity hactivity, sourceVarianceSum,
      ← ht.sum_vertices (fun x => heterogeneousMarginal G S activity x * (1 - p x) * d x ^ 2)]
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [(hagree r hr).1, (hagree r hr).2]

noncomputable def sourceRoots (S : Finset V) (parent : V → Option V) : Finset V :=
  S.filter (fun x => parent x = none)

/-- Every non-root is counted by exactly one parent's children sum. -/
theorem SourceMessages.sum_children {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    (f : V → ℝ) :
    (∑ x ∈ S, ∑ y ∈ sourceChildren S parent x, f y) =
      (∑ y ∈ S, f y) - ∑ y ∈ sourceRoots S parent, f y := by
  classical
  simp only [sourceChildren, sourceRoots, sum_filter]
  rw [sum_comm, ← sum_sub_distrib]
  apply sum_congr rfl
  intro y hy
  cases hp : parent y with
  | none => simp
  | some x =>
    have hx := (h.parent_mem y hy x hp).1
    simp [hx]

theorem SourceMessages.probability_pos {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    (hactivity : ∀ x ∈ S, 0 < activity x) {x : V} (hx : x ∈ S) : 0 < p x := by
  rw [h.odds x hx]
  refine mul_pos (mul_pos (sub_pos.mpr (h.probability x hx).2) (hactivity x hx)) ?_
  apply prod_pos
  intro y hy
  exact sub_pos.mpr (h.probability y (mem_filter.mp hy).1).2

/-- The genuine local log-odds equation, including arbitrarily many children. -/
theorem SourceMessages.log_odds {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    (hactivity : ∀ x ∈ S, 0 < activity x) {x : V} (hx : x ∈ S) :
    Real.log (p x) - Real.log (1 - p x) = Real.log (activity x) +
      ∑ y ∈ sourceChildren S parent x, Real.log (1 - p y) := by
  have hp := h.probability_pos hactivity hx
  have h1 := sub_pos.mpr (h.probability x hx).2
  have hc : ∀ y ∈ sourceChildren S parent x, 1 - p y ≠ 0 := by
    intro y hy
    exact ne_of_gt (sub_pos.mpr (h.probability y (mem_filter.mp hy).1).2)
  have he := congrArg Real.log (h.odds_eq hx)
  unfold sourceChildProduct at he
  rw [Real.log_div hp.ne' h1.ne', Real.log_mul (hactivity x hx).ne' (prod_ne_zero_iff.mpr hc),
    Real.log_prod hc] at he
  exact he

/-- Exact source log mass. Root corrections have the favorable sign. -/
theorem SourceMessages.log_mass_identity {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    (hactivity : ∀ x ∈ S, 0 < activity x) (lower : ℝ) :
    (∑ x ∈ S, (Real.log (p x) - 2 * Real.log (1 - p x) - Real.log lower)) =
      (∑ x ∈ S, Real.log (activity x)) -
        (∑ x ∈ sourceRoots S parent, Real.log (1 - p x)) - (S.card : ℝ) * Real.log lower := by
  have hp : (∑ x ∈ S, (Real.log (p x) - 2 * Real.log (1 - p x) - Real.log lower)) =
      ∑ x ∈ S, (Real.log (activity x) +
        (∑ y ∈ sourceChildren S parent x, Real.log (1 - p y)) - Real.log (1 - p x) - Real.log lower) := by
    apply sum_congr rfl
    intro x hx
    linarith [h.log_odds hactivity hx]
  rw [hp]
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul]
  rw [h.sum_children (fun x => Real.log (1 - p x))]
  ring

/-- The real forest-source log-mass budget. Activities need not be uniform. -/
theorem SourceMessages.log_mass_nonneg {G : SimpleGraph V} {S : Finset V} {activity a : V → ℝ}
    {parent : V → Option V} {p d : V → ℝ} (h : SourceMessages G S activity a parent p d)
    {lower : ℝ} (hlower : 0 < lower) (hactivity : ∀ x ∈ S, lower ≤ activity x) :
    0 ≤ ∑ x ∈ S, (Real.log (p x) - 2 * Real.log (1 - p x) - Real.log lower) := by
  have hp : ∀ x ∈ S, 0 < activity x := fun x hx => hlower.trans_le (hactivity x hx)
  rw [h.log_mass_identity hp lower]
  have hsum : (S.card : ℝ) * Real.log lower ≤ ∑ x ∈ S, Real.log (activity x) := by
    calc
      _ = ∑ _x ∈ S, Real.log lower := by simp
      _ ≤ _ := sum_le_sum (fun x hx => Real.log_le_log hlower (hactivity x hx))
  have hroot : (∑ x ∈ sourceRoots S parent, Real.log (1 - p x)) ≤ 0 := by
    apply sum_nonpos
    intro x hx
    have hb := h.probability x (mem_filter.mp hx).1
    exact Real.log_nonpos (by linarith) (by linarith)
  linarith

#print axioms SourceElimination.messages
#print axioms exists_forest_source_messages_moments
#print axioms SourceMessages.log_mass_identity
#print axioms SourceMessages.log_mass_nonneg
end ForestUnimodality

