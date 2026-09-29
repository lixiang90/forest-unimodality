import ForestUnimodality.HereditaryRank
import ForestUnimodality.GraphCore
import Mathlib.Data.Fintype.EquivFin

/-! Actual vertex subsets encoded by disjoint clique blocks. No graph-count
ratio is assumed: the configuration family and its counting bijection are
constructed from the blocks. -/

namespace ForestUnimodality.BlockRankEncoding

open Finset HereditaryRank
open Classical

variable {V : Type*} [DecidableEq V]

noncomputable def vertex (B : Finset V) (i : Fin B.card) : V := (B.equivFin.symm i).val

omit [DecidableEq V] in
theorem vertex_mem (B : Finset V) (i : Fin B.card) : vertex B i ∈ B :=
  (B.equivFin.symm i).property

omit [DecidableEq V] in
theorem vertex_injective (B : Finset V) : Function.Injective (vertex B) := by
  intro i j h
  exact B.equivFin.symm.injective (Subtype.ext h)

noncomputable def selection (B : Finset V) : Option (Fin B.card) → Finset V
  | none => ∅
  | some i => {vertex B i}

omit [DecidableEq V] in
theorem selection_subset (B : Finset V) (o : Option (Fin B.card)) : selection B o ⊆ B := by
  cases o with
  | none => simp [selection]
  | some i => simpa [selection] using vertex_mem B i

omit [DecidableEq V] in
theorem selection_injective (B : Finset V) : Function.Injective (selection B) := by
  intro o p h
  cases o with
  | none => cases p <;> simp_all [selection]
  | some i =>
    cases p with
    | none => simp_all [selection]
    | some j =>
      have h' : vertex B i = vertex B j := by simpa [selection] using h
      exact congrArg some (vertex_injective B h')

noncomputable def decode : (Bs : List (Finset V)) → Config (Bs.map Finset.card) → Finset V
  | [], _ => ∅
  | B :: Bs, (o, x) => selection B o ∪ decode Bs x

@[simp] theorem decode_cons (B : Finset V) (Bs : List (Finset V))
    (x : Config ((B :: Bs).map Finset.card)) :
    decode (B :: Bs) x = selection B x.1 ∪ decode Bs x.2 := by
  rcases x with ⟨o, x⟩
  rfl

theorem mem_decode_cover (Bs : List (Finset V)) (x : Config (Bs.map Finset.card))
    {v : V} (hv : v ∈ decode Bs x) : ∃ B ∈ Bs, v ∈ B := by
  induction Bs with
  | nil => simp [decode] at hv
  | cons B Bs ih =>
    rcases mem_union.mp hv with h | h
    · exact ⟨B, by simp, selection_subset B x.1 h⟩
    · obtain ⟨C, hC, hvC⟩ := ih x.2 h
      exact ⟨C, by simp [hC], hvC⟩

theorem head_disjoint_decode {B : Finset V} {Bs : List (Finset V)}
    (hBs : (B :: Bs).Pairwise Disjoint) (x : Config (Bs.map Finset.card)) :
    Disjoint B (decode Bs x) := by
  apply Finset.disjoint_left.mpr
  intro v hvB hvx
  obtain ⟨C, hC, hvC⟩ := mem_decode_cover Bs x hvx
  exact Finset.disjoint_left.mp ((List.pairwise_cons.mp hBs).1 C hC) hvB hvC

theorem decode_card {Bs : List (Finset V)} (hBs : Bs.Pairwise Disjoint)
    (x : Config (Bs.map Finset.card)) : ((decode Bs x).card : ℤ) = rank x := by
  induction Bs with
  | nil => simp [decode, rank]
  | cons B Bs ih =>
    have htail := (List.pairwise_cons.mp hBs).2
    have hdis := (head_disjoint_decode hBs x.2).mono_left (selection_subset B x.1)
    rw [decode_cons, Finset.card_union_of_disjoint hdis, Nat.cast_add, ih htail]
    rcases x with ⟨o, x⟩
    cases o <;> simp [selection, rank]

theorem decode_mono {Bs : List (Finset V)} {x y : Config (Bs.map Finset.card)}
    (hxy : Below x y) : decode Bs x ⊆ decode Bs y := by
  induction Bs with
  | nil => simp [decode]
  | cons B Bs ih =>
    have hhead : selection B x.1 ⊆ selection B y.1 := by
      rcases hxy.1 with h | h
      · rw [h]; simp [selection]
      · rw [h]
    exact union_subset_union hhead (ih hxy.2)

theorem decode_inter_head {B : Finset V} {Bs : List (Finset V)}
    (hBs : (B :: Bs).Pairwise Disjoint) (x : Config ((B :: Bs).map Finset.card)) :
    decode (B :: Bs) x ∩ B = selection B x.1 := by
  ext v
  simp only [decode_cons, mem_inter, mem_union]
  constructor
  · rintro ⟨h | h, hvB⟩
    · exact h
    · exact False.elim (Finset.disjoint_left.mp (head_disjoint_decode hBs x.2) hvB h)
  · intro h
    exact ⟨Or.inl h, selection_subset B x.1 h⟩

theorem decode_sdiff_head {B : Finset V} {Bs : List (Finset V)}
    (hBs : (B :: Bs).Pairwise Disjoint) (x : Config ((B :: Bs).map Finset.card)) :
    decode (B :: Bs) x \ B = decode Bs x.2 := by
  ext v
  simp only [decode_cons, mem_sdiff, mem_union]
  constructor
  · rintro ⟨h | h, hvB⟩
    · exact False.elim (hvB (selection_subset B x.1 h))
    · exact h
  · intro h
    exact ⟨Or.inr h, fun hvB => Finset.disjoint_left.mp (head_disjoint_decode hBs x.2) hvB h⟩

theorem decode_injective {Bs : List (Finset V)} (hBs : Bs.Pairwise Disjoint) :
    Function.Injective (decode Bs) := by
  induction Bs with
  | nil => intro x y _; cases x; cases y; rfl
  | cons B Bs ih =>
    intro x y h
    have hh := congrArg (fun T => T ∩ B) h
    rw [decode_inter_head hBs, decode_inter_head hBs] at hh
    have ht := congrArg (fun T => T \ B) h
    rw [decode_sdiff_head hBs, decode_sdiff_head hBs] at ht
    exact Prod.ext (selection_injective B hh) (ih (List.pairwise_cons.mp hBs).2 ht)

omit [DecidableEq V] in
theorem exists_selection (B T : Finset V) (hsub : T ⊆ B)
    (hsmall : ∀ u ∈ T, ∀ v ∈ T, u = v) : ∃ o, selection B o = T := by
  by_cases hT : T.Nonempty
  · obtain ⟨v, hv⟩ := hT
    have hTv : T = {v} := by
      ext u
      simp only [mem_singleton]
      exact ⟨fun hu => hsmall u hu v hv, fun h => h ▸ hv⟩
    refine ⟨some (B.equivFin ⟨v, hsub hv⟩), ?_⟩
    simp [selection, vertex, hTv]
  · exact ⟨none, by simpa [selection] using (Finset.not_nonempty_iff_eq_empty.mp hT).symm⟩

/-- Every independent set covered by clique blocks has an actual configuration. -/
theorem exists_decode_of_independent (G : SimpleGraph V) (Bs : List (Finset V))
    (hclique : ∀ B ∈ Bs, ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v)
    (T : Finset V) (hind : G.IsIndepSet (T : Set V))
    (hcover : ∀ v ∈ T, ∃ B ∈ Bs, v ∈ B) :
    ∃ x : Config (Bs.map Finset.card), decode Bs x = T := by
  induction Bs generalizing T with
  | nil =>
    have hT : T = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      obtain ⟨B, hB, _⟩ := hcover v hv
      simp at hB
    exact ⟨(), hT.symm⟩
  | cons B Bs ih =>
    obtain ⟨o, ho⟩ := exists_selection B (T ∩ B) (inter_subset_right) (by
      intro u hu v hv
      by_contra hne
      exact hind (mem_inter.mp hu).1 (mem_inter.mp hv).1 hne
        (hclique B (by simp) u (mem_inter.mp hu).2 v (mem_inter.mp hv).2 hne))
    have htail : G.IsIndepSet ((T \ B : Finset V) : Set V) := by
      intro u hu v hv hne
      exact hind (mem_sdiff.mp hu).1 (mem_sdiff.mp hv).1 hne
    obtain ⟨x, hx⟩ := ih (fun C hC => hclique C (by simp [hC])) (T \ B) htail (by
      intro v hv
      obtain ⟨C, hC, hvC⟩ := hcover v (mem_sdiff.mp hv).1
      rcases List.mem_cons.mp hC with rfl | hC
      · exact False.elim ((mem_sdiff.mp hv).2 hvC)
      · exact ⟨C, hC, hvC⟩)
    refine ⟨(o, x), ?_⟩
    rw [decode_cons, ho, hx]
    simpa only [union_comm] using Finset.sdiff_union_inter T B

def independentFamily (G : SimpleGraph V) (Bs : List (Finset V))
    (x : Config (Bs.map Finset.card)) : Prop := G.IsIndepSet (decode Bs x : Set V)

theorem independentFamily_hereditary (G : SimpleGraph V) (Bs : List (Finset V)) :
    Hereditary (independentFamily G Bs) := by
  intro x y hxy hy u hu v hv hne
  exact hy (decode_mono hxy hu) (decode_mono hxy hv) hne

theorem independentLayer_image (G : SimpleGraph V) (S : Finset V)
    (Bs : List (Finset V)) (hdis : Bs.Pairwise Disjoint)
    (hclique : ∀ B ∈ Bs, ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v)
    (hcover : ∀ v, v ∈ S ↔ ∃ B ∈ Bs, v ∈ B) (k : ℕ) :
    (rankLayer (independentFamily G Bs) (k : ℤ)).image (decode Bs) =
      (independentSubsets G S).filter (fun T => T.card = k) := by
  ext T
  constructor
  · intro hT
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hT
    obtain ⟨hind, hrank⟩ := (mem_rankLayer _ _ _).mp hx
    apply mem_filter.mpr
    refine ⟨mem_independentSubsets.mpr ⟨?_, hind⟩, ?_⟩
    · intro v hv
      exact (hcover v).mpr (mem_decode_cover Bs x hv)
    · exact_mod_cast (decode_card hdis x).trans hrank
  · intro hT
    obtain ⟨hT, hcard⟩ := mem_filter.mp hT
    obtain ⟨hsub, hind⟩ := mem_independentSubsets.mp hT
    obtain ⟨x, hx⟩ := exists_decode_of_independent G Bs hclique T hind
      (fun v hv => (hcover v).mp (hsub hv))
    apply mem_image.mpr
    refine ⟨x, (mem_rankLayer _ _ _).mpr ⟨?_, ?_⟩, hx⟩
    · simpa only [independentFamily, hx] using hind
    · rw [← decode_card hdis x, hx, hcard]

theorem rankCount_independentFamily (G : SimpleGraph V) (S : Finset V)
    (Bs : List (Finset V)) (hdis : Bs.Pairwise Disjoint)
    (hclique : ∀ B ∈ Bs, ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v)
    (hcover : ∀ v, v ∈ S ↔ ∃ B ∈ Bs, v ∈ B) (k : ℕ) :
    rankCount (independentFamily G Bs) (k : ℤ) = (countIndependent G S k : ℝ) := by
  unfold rankCount countIndependent
  rw [← independentLayer_image G S Bs hdis hclique hcover k,
    Finset.card_image_of_injective _ (decode_injective hdis)]

theorem normalized_countIndependent_of_blocks (G : SimpleGraph V) (S : Finset V)
    (Bs : List (Finset V)) (hdis : Bs.Pairwise Disjoint)
    (hclique : ∀ B ∈ Bs, ∀ u ∈ B, ∀ v ∈ B, u ≠ v → G.Adj u v)
    (hcover : ∀ v, v ∈ S ↔ ∃ B ∈ Bs, v ∈ B)
    (hpos : ∀ B ∈ Bs, 0 < B.card) (k : ℕ) :
    (countIndependent G S (k + 1) : ℝ) *
        referenceRank ((Bs.map Finset.card).map (fun d : ℕ => (d : ℝ))) (k : ℤ) ≤
      (countIndependent G S k : ℝ) *
        referenceRank ((Bs.map Finset.card).map (fun d : ℕ => (d : ℝ))) ((k + 1 : ℕ) : ℤ) := by
  have hp : ∀ d ∈ Bs.map Finset.card, 0 < d := by
    intro d hd
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hd
    exact hpos B hB
  have h := normalized_adjacent_rank (Bs.map Finset.card) hp
    (independentFamily G Bs) (independentFamily_hereditary G Bs) (k : ℤ)
  have hk : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hk, rankCount_independentFamily G S Bs hdis hclique hcover,
    rankCount_independentFamily G S Bs hdis hclique hcover] at h
  exact h

#print axioms decode_card
#print axioms decode_injective
#print axioms decode_mono
#print axioms rankCount_independentFamily
#print axioms normalized_countIndependent_of_blocks

end ForestUnimodality.BlockRankEncoding
