import ForestUnimodality.RootedBlockAttachment
import ForestUnimodality.GraphIsomorphismStats
import ForestUnimodality.TerminalContextCertificate
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! Smaller path contexts use genuinely new vertices. The induction premise
quantifies over every graph in the same universe, not only subsets of a fixed
ambient graph. -/
namespace ForestUnimodality
open Finset
universe u

def GlobalSmallerMeanHyp (n : ℕ) : Prop :=
  ∀ (W : Type u) [DecidableEq W] (G : SimpleGraph W) (S : Finset W),
    S.card < n → G.IsAcyclic →
      0 ≤ adjustedMeanPotential G S (independenceNumberOn G S)

theorem GlobalSmallerMeanHyp.same_graph {n : ℕ} (h : GlobalSmallerMeanHyp.{u} n)
    {V : Type u} [DecidableEq V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) (hcard : S.card = n) :
    ∀ T ⊆ S, T.card < S.card → ∀ I, IsMaximumIndependentOn G T I →
      0 ≤ adjustedMeanPotential G T I.card := by
  intro T _ hT I hI
  rw [hI.card_eq_independenceNumberOn]
  exact h V G T (hcard ▸ hT) hG

namespace FreshPathContext

theorem sum_isAcyclic {V W : Type*} {G : SimpleGraph V} {K : SimpleGraph W}
    (hG : G.IsAcyclic) (hK : K.IsAcyclic) : (G.sum K).IsAcyclic := by
  classical
  intro x p hp
  cases x with
  | inl x =>
    have hs : ∀ y ∈ p.support, y ∈ Set.range (Sum.inl : V → V ⊕ W) := by
      intro y hy
      cases y with
      | inl y => exact ⟨y, rfl⟩
      | inr y => exact False.elim (SimpleGraph.not_reachable_sum_inl_inr x y
          (p.takeUntil _ hy).reachable)
    have hi := (SimpleGraph.Embedding.sumInl (G := G) (H := K)).isoInduceRange.isAcyclic_iff.mp hG
    apply hi (p.induce _ hs)
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa [SimpleGraph.Walk.map_induce, SimpleGraph.Embedding.induce] using hp
  | inr x =>
    have hs : ∀ y ∈ p.support, y ∈ Set.range (Sum.inr : W → V ⊕ W) := by
      intro y hy
      cases y with
      | inr y => exact ⟨y, rfl⟩
      | inl y => exact False.elim (SimpleGraph.not_reachable_sum_inl_inr y x
          (p.takeUntil _ hy).reachable.symm)
    have hi := (SimpleGraph.Embedding.sumInr (G := G) (H := K)).isoInduceRange.isAcyclic_iff.mp hK
    apply hi (p.induce _ hs)
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce _).toHom)
    simpa [SimpleGraph.Walk.map_induce, SimpleGraph.Embedding.induce] using hp

/-- A finite path on `0,...,n-1`, with all other natural numbers isolated. -/
def segmentGraph (n : ℕ) : SimpleGraph ℕ where
  Adj i j := i < n ∧ j < n ∧ (i + 1 = j ∨ j + 1 = i)
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => by omega⟩

theorem segmentGraph_zero : segmentGraph 0 = ⊥ := by
  ext i j
  simp [segmentGraph]

theorem segmentGraph_one : segmentGraph 1 = ⊥ := by
  ext i j
  simp only [segmentGraph, SimpleGraph.bot_adj, iff_false]
  omega

theorem segmentGraph_succ (n : ℕ) :
    segmentGraph (n + 2) = segmentGraph (n + 1) ⊔ SimpleGraph.edge n (n + 1) := by
  ext i j
  simp only [segmentGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  omega

theorem segmentGraph_isAcyclic (n : ℕ) : (segmentGraph n).IsAcyclic := by
  induction n using Nat.twoStepInduction with
  | zero => rw [segmentGraph_zero]; exact SimpleGraph.isAcyclic_bot
  | one => rw [segmentGraph_one]; exact SimpleGraph.isAcyclic_bot
  | more n _ ih =>
    rw [segmentGraph_succ]
    apply ih.sup_edge_of_not_reachable
    rintro ⟨p⟩
    have hp := p.reverse
    cases hp with
    | cons hadj tail => exact (Nat.lt_irrefl (n + 1)) hadj.1

variable {V : Type u} [DecidableEq V]

/-- The old host and the new path are in different summands. -/
def graph (G : SimpleGraph V) (v : V) (n : ℕ) : SimpleGraph (V ⊕ ℕ) :=
  G.sum (segmentGraph n) ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr (n - 1))

omit [DecidableEq V] in
theorem graph_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic) (v : V) (n : ℕ) :
    (graph G v n).IsAcyclic :=
  (sum_isAcyclic hG (segmentGraph_isAcyclic n)).sup_edge_of_not_reachable
    (SimpleGraph.not_reachable_sum_inl_inr v (n - 1))

def host (H : Finset V) : Finset (V ⊕ ℕ) := H.map Function.Embedding.inl
def block (n : ℕ) : Finset (V ⊕ ℕ) := (range n).map Function.Embedding.inr

omit [DecidableEq V] in
@[simp] theorem mem_host (H : Finset V) (x : V) : Sum.inl x ∈ host H ↔ x ∈ H := by
  simp [host]
omit [DecidableEq V] in
@[simp] theorem mem_block (n i : ℕ) : (Sum.inr i : V ⊕ ℕ) ∈ block n ↔ i < n := by
  simp [block]

omit [DecidableEq V] in
theorem attachment (G : SimpleGraph V) (H : Finset V) {v : V} (hv : v ∈ H)
    {n : ℕ} (hn : 0 < n) :
    IsRootedBlockAttachment (graph G v n) (host H) (Sum.inl v) (block n)
      (Sum.inr (n - 1)) := by
  refine ⟨by simpa using hv, by simpa using (by omega : n - 1 < n), ?_, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := mem_map.mp hx
    simp [block] at hy
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hy
    simp [graph, SimpleGraph.edge_adj]

@[simp] theorem block_succ (k : ℕ) :
    (block (k + 1) : Finset (V ⊕ ℕ)) = insert (Sum.inr k) (block k) := by
  simp [block, range_add_one, map_insert]

omit [DecidableEq V] in
@[simp] theorem block_zero : (block 0 : Finset (V ⊕ ℕ)) = ∅ := by
  simp [block]

omit [DecidableEq V] in
@[simp] theorem block_one : (block 1 : Finset (V ⊕ ℕ)) = {Sum.inr 0} := by
  simp [block, range_one]

theorem block_path_aux (G : SimpleGraph V) (v : V) (n k : ℕ) (hk : k < n) :
    PendantPathExtension (graph G v n) {Sum.inr 0} (Sum.inr 0) k
      (block (k + 1)) (Sum.inr k) := by
  induction k with
  | zero => simpa using (PendantPathExtension.zero (G := graph G v n)
      (mem_singleton_self (Sum.inr 0)))
  | succ k ih =>
    have hh := ih (by omega)
    rw [block_succ]
    apply hh.succ (Sum.inr (k + 1)) (by simp)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hx
    simp only [mem_range] at hi
    simp only [graph, SimpleGraph.sup_adj, SimpleGraph.sum_adj,
      SimpleGraph.edge_adj, segmentGraph, Function.Embedding.inr_apply,
      Sum.inr.injEq, Sum.inr_ne_inl, false_and, and_false, or_false]
    omega

theorem block_path (G : SimpleGraph V) (v : V) (n : ℕ) (hn : 0 < n) :
    PendantPathExtension (graph G v n) {Sum.inr 0} (Sum.inr 0) (n - 1)
      (block n) (Sum.inr (n - 1)) := by
  have h := block_path_aux G v n (n - 1) (by omega)
  simpa only [Nat.sub_add_cancel hn] using h

theorem block_state (G : SimpleGraph V) (v : V) (n : ℕ) (hn : 0 < n) :
    actualBlockState (graph G v n) (block n) (Sum.inr (n - 1)) =
      TerminalBlockRecurrence.castState (TerminalContextCertificate.pathState n) := by
  rw [(block_path G v n hn).actualBlockState_path]
  rw [TerminalContextCertificate.pathState, TerminalBlockRecurrence.cast_iterate]
  congr 1
  norm_num [TerminalBlockRecurrence.castState]

/-- The old finite induced host is preserved exactly in the new ambient graph. -/
noncomputable def hostIso (G : SimpleGraph V) (H : Finset V) (v : V) (n : ℕ) :
    G.induce (H : Set V) ≃g (graph G v n).induce (host H : Set (V ⊕ ℕ)) := by
  let f : {x : V // x ∈ H} → {x : V ⊕ ℕ // x ∈ host H} :=
    fun x => ⟨Sum.inl x.val, by simp [x.property]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact Sum.inl.inj (congrArg Subtype.val he)
    · intro y
      obtain ⟨x, hx, hxy⟩ := mem_map.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine { toEquiv := Equiv.ofBijective f hf, map_rel_iff' := ?_ }
  intro x y
  change (graph G v n).Adj (Sum.inl x.val) (Sum.inl y.val) ↔ G.Adj x.val y.val
  simp [graph, SimpleGraph.edge_adj]

omit [DecidableEq V] in
@[simp] theorem hostIso_root (G : SimpleGraph V) (H : Finset V) {v : V}
    (hv : v ∈ H) (n : ℕ) :
    hostIso G H v n ⟨v, hv⟩ = ⟨Sum.inl v, by simpa using hv⟩ := rfl

theorem context_card (H : Finset V) (n : ℕ) :
    (host H ∪ block n).card = H.card + n := by
  have hd : Disjoint (host H) (block n) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := mem_map.mp hx
    simp [block] at hy
  rw [card_union_of_disjoint hd]
  simp [host, block]

/-- A smaller new path context is legitimate under strong induction over all
forests. The root state in this conclusion is the HOST'S ACTUAL state. -/
theorem path_residual_nonneg {N : ℕ} (hsmaller : GlobalSmallerMeanHyp.{u} N)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (H : Finset V) {v : V} (hv : v ∈ H)
    (j : ℕ) (hj : 0 < j) (hsize : H.card + j < N) :
    let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
    0 ≤ TerminalBlockRecurrence.E
      (TerminalBlockRecurrence.castState (TerminalContextCertificate.pathState j))
      (rootDefect G H v : ℝ)
      (r * adjustedMeanPotential G H (independenceNumberOn G H))
      (adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) r := by
  have hmean := hsmaller (V ⊕ ℕ) (graph G v j) (host H ∪ block j)
    (by simpa only [context_card] using hsize) (graph_isAcyclic G hG v j)
  have he := (attachment G H hv hj).adjustedMean_nonneg_iff.mp hmean
  let e := hostIso G H v j
  have hroot : e ⟨v, hv⟩ = ⟨Sum.inl v, by simpa using hv⟩ := rfl
  let ed := InducedIso.eraseRoot e hv (by simpa using hv) hroot
  have hdef : rootDefect (graph G v j) (host H) (Sum.inl v) = rootDefect G H v := by
    unfold rootDefect
    rw [← InducedIso.independenceNumber_eq e, ← InducedIso.independenceNumber_eq ed]
  dsimp only at he ⊢
  rw [block_state G v j hj, hdef, ← InducedIso.partitionFunction_eq e (2 : ℝ),
    ← InducedIso.partitionFunction_eq ed (2 : ℝ), ← InducedIso.adjustedMean_eq e,
    ← InducedIso.adjustedMean_eq ed] at he
  exact he

/-- The source certificate's chosen state is usable once its equality to the
actual host state has been justified structurally. -/
theorem path_residual_nonneg_of_state {N : ℕ} (hsmaller : GlobalSmallerMeanHyp.{u} N)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (H : Finset V) {v : V} (hv : v ∈ H)
    (j : ℕ) (hj : 0 < j) (hsize : H.card + j < N) (d : ℝ)
    (hd : d = (rootDefect G H v : ℝ)) :
    let r := partitionFunction G H (2 : ℝ) / partitionFunction G (H.erase v) 2
    0 ≤ TerminalBlockRecurrence.E
      (TerminalBlockRecurrence.castState (TerminalContextCertificate.pathState j)) d
      (r * adjustedMeanPotential G H (independenceNumberOn G H))
      (adjustedMeanPotential G (H.erase v) (independenceNumberOn G (H.erase v))) r := by
  rw [hd]
  exact path_residual_nonneg hsmaller G hG H hv j hj hsize

#print axioms sum_isAcyclic
#print axioms graph_isAcyclic
#print axioms attachment
#print axioms block_state
#print axioms hostIso
#print axioms path_residual_nonneg
end FreshPathContext
end ForestUnimodality
