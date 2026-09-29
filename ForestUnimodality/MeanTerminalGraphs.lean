import ForestUnimodality.MeanTerminalClosure
import ForestUnimodality.AdjustedMeanPath
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.FinCases

/-!
The actual rooted graphs behind the eight terminal-closure parameters.

T33 and T35 are paths on seven and nine vertices rooted at vertex three;
deleting that root leaves arms with (3,3) and (3,5) vertices respectively.
The other six graphs are even paths rooted at an endpoint. All statistics
below are computed over the actual independent subsets of these graphs.
-/

namespace ForestUnimodality.MeanTerminalGraphs

open Finset
open scoped BigOperators

/-- A computational presentation of the standard finite path graph. -/
def actualPath (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance (n : ℕ) : DecidableRel (actualPath n).Adj := fun u v =>
  inferInstanceAs (Decidable (u.val + 1 = v.val ∨ v.val + 1 = u.val))

theorem actualPath_eq_pathGraph (n : ℕ) : actualPath n = SimpleGraph.pathGraph n := by
  ext u v
  exact SimpleGraph.pathGraph_adj.symm

/-- Independent-set filtering with the graph's supplied decision procedure.
The equality theorem below connects this executable presentation to GraphCore. -/
def computableIndependents {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : Finset (Finset V) :=
  S.powerset.filter fun J => G.IsIndepSet (J : Set V)

theorem computableIndependents_eq {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    computableIndependents G S = independentSubsets G S := by
  ext J
  simp [computableIndependents, mem_independentSubsets]

structure RootStatistics where
  partition : ℕ
  firstMoment : ℕ
  deletedPartition : ℕ
  deletedFirstMoment : ℕ
  independence : ℕ
  deletedIndependence : ℕ
  deriving DecidableEq, Repr

def computeStatistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) : RootStatistics where
  partition := ∑ J ∈ computableIndependents G S, 2^J.card
  firstMoment := ∑ J ∈ computableIndependents G S, J.card * 2^J.card
  deletedPartition := ∑ J ∈ computableIndependents G (S.erase root), 2^J.card
  deletedFirstMoment := ∑ J ∈ computableIndependents G (S.erase root), J.card * 2^J.card
  independence := (computableIndependents G S).sup Finset.card
  deletedIndependence := (computableIndependents G (S.erase root)).sup Finset.card

theorem partition_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    partitionFunction G S (2 : ℝ) = ((computeStatistics G S root).partition : ℝ) := by
  simp only [partitionFunction, computeStatistics, computableIndependents_eq,
    Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

theorem firstMoment_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    hardCoreMomentNumerator G S 1 (2 : ℝ) =
      ((computeStatistics G S root).firstMoment : ℝ) := by
  simp only [hardCoreMomentNumerator, computeStatistics, computableIndependents_eq,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_one]

theorem deletedPartition_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    partitionFunction G (S.erase root) (2 : ℝ) =
      ((computeStatistics G S root).deletedPartition : ℝ) := by
  simp only [partitionFunction, computeStatistics, computableIndependents_eq,
    Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]

theorem deletedFirstMoment_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    hardCoreMomentNumerator G (S.erase root) 1 (2 : ℝ) =
      ((computeStatistics G S root).deletedFirstMoment : ℝ) := by
  simp only [hardCoreMomentNumerator, computeStatistics, computableIndependents_eq,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_one]

theorem independence_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    independenceNumberOn G S = (computeStatistics G S root).independence := by
  simp only [independenceNumberOn, computeStatistics, computableIndependents_eq]

theorem deletedIndependence_eq_statistics {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (root : V) :
    independenceNumberOn G (S.erase root) = (computeStatistics G S root).deletedIndependence := by
  simp only [independenceNumberOn, computeStatistics, computableIndependents_eq]

def branchOrder (i : Fin 8) : ℕ := match i.val with
  | 0 => 7 | 1 => 9 | 2 => 2 | 3 => 4 | 4 => 6 | 5 => 8 | 6 => 10 | _ => 12

def branchGraph (i : Fin 8) : SimpleGraph (Fin (branchOrder i)) := actualPath (branchOrder i)

instance (i : Fin 8) : DecidableRel (branchGraph i).Adj :=
  inferInstanceAs (DecidableRel (actualPath (branchOrder i)).Adj)

def branchRoot (i : Fin 8) : Fin (branchOrder i) :=
  ⟨if i.val < 2 then 3 else 0, by fin_cases i <;> decide⟩

/-- The independently reconstructed expected integer statistics. -/
def expectedStatistics (i : Fin 8) : RootStatistics := match i.val with
  | 0 => ⟨171, 438, 121, 308, 4, 4⟩
  | 1 => ⟨683, 2202, 473, 1504, 5, 5⟩
  | 2 => ⟨5, 4, 3, 2, 1, 1⟩
  | 3 => ⟨21, 32, 11, 14, 2, 2⟩
  | 4 => ⟨85, 188, 43, 82, 3, 3⟩
  | 5 => ⟨341, 984, 171, 438, 4, 4⟩
  | 6 => ⟨1365, 4852, 683, 2202, 5, 5⟩
  | _ => ⟨5461, 23056, 2731, 10622, 6, 6⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actual_branch_statistics (i : Fin 8) :
    computeStatistics (branchGraph i) univ (branchRoot i) = expectedStatistics i := by
  fin_cases i <;> decide +kernel

/-- Exact ratio of the actual graph partition function to its root deletion. -/
theorem actual_branch_ratio (i : Fin 8) :
    partitionFunction (branchGraph i) univ (2 : ℝ) /
      partitionFunction (branchGraph i) (univ.erase (branchRoot i)) (2 : ℝ) =
        (MeanTerminalClosure.branchRatio i.val : ℝ) := by
  rw [partition_eq_statistics (branchGraph i) univ (branchRoot i),
    deletedPartition_eq_statistics (branchGraph i) univ (branchRoot i),
    actual_branch_statistics]
  fin_cases i <;> norm_num [expectedStatistics, MeanTerminalClosure.branchRatio]

/-- The table's a-coordinate is the actual activity-two adjusted mean. -/
theorem actual_branch_excess (i : Fin 8) :
    adjustedMeanPotential (branchGraph i) univ (independenceNumberOn (branchGraph i) univ) =
      (MeanTerminalClosure.branchExcess i.val : ℝ) := by
  unfold adjustedMeanPotential hardCoreMean
  rw [partition_eq_statistics (branchGraph i) univ (branchRoot i),
    firstMoment_eq_statistics (branchGraph i) univ (branchRoot i),
    independence_eq_statistics (branchGraph i) univ (branchRoot i),
    actual_branch_statistics]
  fin_cases i <;> norm_num [expectedStatistics, branchOrder, MeanTerminalClosure.branchExcess]

/-- The b-coordinate subtracts the ORIGINAL order and independence number.
It is not the adjusted mean of the root-deleted graph without correction. -/
theorem actual_branch_deleted_excess (i : Fin 8) :
    3 * hardCoreMean (branchGraph i) (univ.erase (branchRoot i)) 2 -
      (independenceNumberOn (branchGraph i) univ : ℝ) -
      29 * ((univ : Finset (Fin (branchOrder i))).card : ℝ) / 60 =
        (MeanTerminalClosure.branchDeletedExcess i.val : ℝ) := by
  unfold hardCoreMean
  rw [deletedPartition_eq_statistics (branchGraph i) univ (branchRoot i),
    deletedFirstMoment_eq_statistics (branchGraph i) univ (branchRoot i),
    independence_eq_statistics (branchGraph i) univ (branchRoot i),
    actual_branch_statistics]
  fin_cases i <;>
    norm_num [expectedStatistics, branchOrder, MeanTerminalClosure.branchDeletedExcess]

/-- Every one of the eight actual roots has cardinality state zero. -/
theorem actual_branch_root_state_zero (i : Fin 8) :
    independenceNumberOn (branchGraph i) univ =
      independenceNumberOn (branchGraph i) (univ.erase (branchRoot i)) := by
  rw [independence_eq_statistics (branchGraph i) univ (branchRoot i),
    deletedIndependence_eq_statistics (branchGraph i) univ (branchRoot i),
    actual_branch_statistics]
  fin_cases i <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem actual_branch_edge_count (i : Fin 8) :
    (branchGraph i).edgeFinset.card + 1 = branchOrder i := by
  fin_cases i <;> decide +kernel

/-- These are actual finite trees, in addition to having the required
independent-set statistics. Connectedness comes from the standard path graph,
and its exact edge count rules out cycles. -/
theorem actual_branch_isTree (i : Fin 8) : (branchGraph i).IsTree := by
  letI : Nonempty (Fin (branchOrder i)) := ⟨branchRoot i⟩
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · constructor
    rw [branchGraph, actualPath_eq_pathGraph]
    exact SimpleGraph.pathGraph_preconnected _
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    exact actual_branch_edge_count i

#print axioms actual_branch_statistics
#print axioms computableIndependents_eq
#print axioms actual_branch_ratio
#print axioms actual_branch_excess
#print axioms actual_branch_deleted_excess
#print axioms actual_branch_root_state_zero
#print axioms actual_branch_isTree

end ForestUnimodality.MeanTerminalGraphs
