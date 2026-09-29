import ForestUnimodality.ShortLegData

/-! Exhaustive rational arithmetic for the short-leg part of the mean proof.
Actual graph decompositions and the identification of their statistics are
separate proved interfaces; this module does not assert graph coverage. -/
namespace ForestUnimodality.ShortLegData
open MeanTerminalClosure

def legLength (odd : Bool) (i : ℕ) : ℕ := if odd then 2 * i + 1 else 2 * i + 2
def legBound (odd : Bool) : ℕ := if odd then 7 else 6
def legsOf (odd : Bool) (fan : List ℕ) : List ℕ := fan.map (legLength odd)

/-- The sixteen remaining three-odd-leg types, written in descending order. -/
def oddTriples : List (List ℕ) :=
  [[5,5,3], [7,5,3], [9,5,3], [7,7,3],
   [5,5,5], [7,5,5], [9,5,5], [11,5,5],
   [7,7,5], [9,7,5], [11,7,5], [9,9,5],
   [7,7,7], [9,7,7], [11,7,7], [9,9,7]]

def exceptional (odd : Bool) (legs : List ℕ) (delta : ℕ) : Bool :=
  if odd then decide (delta = 0 ∧ (legs.length = 2 ∨ legs ∈ oddTriples))
  else decide (delta = 1 ∧ legs = [2,2])

def endpointCheck (odd : Bool) (fan : List ℕ) (delta : ℕ) : Bool :=
  let legs := legsOf odd fan
  if exceptional odd legs delta then
    decide (residual odd legs delta 1 < 0 ∨ residual odd legs delta 3 < 0)
  else decide (0 < residual odd legs delta 1 ∧ 0 < residual odd legs delta 3)

def finiteLegCheck : Bool := [false, true].all fun odd =>
  ([2,3] : List ℕ).all fun m =>
    (enumerateFans m (legBound odd)).all fun fan =>
      ([0,1] : List ℕ).all (endpointCheck odd fan)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finiteLegCheck_eq_true : finiteLegCheck = true := by decide +kernel

theorem finite_leg_classification (odd : Bool) (fan : List ℕ) (delta : ℕ)
    (hm : fan.length = 2 ∨ fan.length = 3)
    (hdesc : DescendingBounded (legBound odd) fan) (hd : delta ≤ 1) :
    if exceptional odd (legsOf odd fan) delta then
      residual odd (legsOf odd fan) delta 1 < 0 ∨
        residual odd (legsOf odd fan) delta 3 < 0
    else 0 < residual odd (legsOf odd fan) delta 1 ∧
        0 < residual odd (legsOf odd fan) delta 3 := by
  have ho : odd ∈ [false, true] := by cases odd <;> simp
  have hlen : fan.length ∈ ([2,3] : List ℕ) := by simpa using hm
  have hdelta : delta ∈ ([0,1] : List ℕ) := by simp; omega
  have h := List.all_eq_true.mp finiteLegCheck_eq_true odd ho
  have h := List.all_eq_true.mp h fan.length hlen
  have h := List.all_eq_true.mp h fan ((mem_enumerateFans _ _ _).mpr ⟨rfl, hdesc⟩)
  have h := List.all_eq_true.mp h delta hdelta
  by_cases he : exceptional odd (legsOf odd fan) delta = true
  · simpa [endpointCheck, he] using h
  · simpa [endpointCheck, he] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_leg_counts :
    (([false, true].flatMap fun odd => ([2,3] : List ℕ).flatMap fun m =>
      (enumerateFans m (legBound odd)).flatMap fun fan =>
        ([0,1] : List ℕ).map fun delta => (odd, legsOf odd fan, delta)).length = 378) ∧
    (([false, true].flatMap fun odd => ([2,3] : List ℕ).flatMap fun m =>
      (enumerateFans m (legBound odd)).flatMap fun fan =>
        ([0,1] : List ℕ).map fun delta => (odd, legsOf odd fan, delta)).filter
          fun x => exceptional x.1 x.2.1 x.2.2).length = 45 := by decide +kernel

def spiderBases : List (List ℕ) :=
  (([3,4] : List ℕ).flatMap fun m => (enumerateFans m 7).map (legsOf true)) ++ [[2,2,2]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem spiderBases_check : spiderBases.all (fun legs => decide (0 < spiderNumerator legs)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem spiderBases_count : spiderBases.length = 295 := by decide +kernel

theorem spider_base_positive (legs : List ℕ) (h : legs ∈ spiderBases) :
    0 < spiderNumerator legs := by
  exact of_decide_eq_true (List.all_eq_true.mp spiderBases_check legs h)

theorem spider_odd_base_positive (fan : List ℕ)
    (hm : fan.length = 3 ∨ fan.length = 4) (hd : DescendingBounded 7 fan) :
    0 < spiderNumerator (legsOf true fan) := by
  apply spider_base_positive
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨fan.length, by simpa using hm, ?_⟩
  exact List.mem_map.mpr ⟨fan, (mem_enumerateFans _ _ _).mpr ⟨rfl, hd⟩, rfl⟩

/-- A smaller direct closure basis: every same-parity short spider of degree
at most three, including the singleton and all paths. -/
def smallSpiderBases : List (List ℕ) := [[]] ++
  ([false, true].flatMap fun odd => ([1,2,3] : List ℕ).flatMap fun m =>
    (enumerateFans m (legBound odd)).map (legsOf odd))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallSpiderBases_check :
    smallSpiderBases.all (fun legs => decide (0 < spiderNumerator legs)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallSpiderBases_count : smallSpiderBases.length = 203 := by decide +kernel

theorem small_spider_base_positive (legs : List ℕ) (h : legs ∈ smallSpiderBases) :
    0 < spiderNumerator legs :=
  of_decide_eq_true (List.all_eq_true.mp smallSpiderBases_check legs h)

theorem small_spider_canonical_positive (odd : Bool) (fan : List ℕ)
    (hm : fan.length ≤ 3) (hd : DescendingBounded (legBound odd) fan) :
    0 < spiderNumerator (legsOf odd fan) := by
  apply small_spider_base_positive
  by_cases hz : fan = []
  · subst fan
    simp [smallSpiderBases, legsOf]
  · apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨odd, by cases odd <;> simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨fan.length, ?_, ?_⟩
    · have hp : 0 < fan.length := List.length_pos_iff.mpr hz
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · exact List.mem_map.mpr ⟨fan, (mem_enumerateFans _ _ _).mpr ⟨rfl, hd⟩, rfl⟩

theorem descending_of_pairwise (bound : ℕ) (fan : List ℕ)
    (hbound : ∀ i ∈ fan, i < bound) (hpair : fan.Pairwise (fun i j => j ≤ i)) :
    DescendingBounded bound fan := by
  induction fan generalizing bound with
  | nil => trivial
  | cons i is ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    exact ⟨hbound i (by simp), ih (i + 1) (fun j hj => by
      have hji := hhead j hj
      omega) htail⟩

theorem small_spider_positive (odd : Bool) (fan : List ℕ)
    (hm : fan.length ≤ 3) (hbound : ∀ i ∈ fan, i < legBound odd) :
    0 < spiderNumerator (legsOf odd fan) := by
  let ordered := fan.mergeSort (fun i j => decide (j ≤ i))
  have hp : ordered.Perm fan := List.mergeSort_perm _ _
  have hdesc : DescendingBounded (legBound odd) ordered := descending_of_pairwise _ _
    (fun i hi => hbound i (hp.mem_iff.mp hi)) (List.pairwise_mergeSort' _ fan)
  have h := small_spider_canonical_positive odd ordered (by rwa [hp.length_eq]) hdesc
  have hmapped : (legsOf odd ordered).Perm (legsOf odd fan) := hp.map (legLength odd)
  rwa [spiderNumerator_perm hmapped] at h

#print axioms finiteLegCheck_eq_true
#print axioms finite_leg_classification
#print axioms finite_leg_counts
#print axioms spiderBases_check
#print axioms spider_base_positive
#print axioms smallSpiderBases_check
#print axioms small_spider_canonical_positive
#print axioms small_spider_positive
end ForestUnimodality.ShortLegData
