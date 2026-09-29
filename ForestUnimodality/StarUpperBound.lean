import ForestUnimodality.EdgeDeletion
import ForestUnimodality.ShiftedChoose

/-!
For a nonempty forest with n vertices and e edges, each independence
coefficient is at most the corresponding coefficient for an e-edge star
together with n-e-1 isolated vertices. All lower-index shifts are guarded.
-/

namespace ForestUnimodality

open Finset

/-- Coefficients of `(1+X)^(n-1) + X*(1+X)^(n-e-1)`. -/
def starBound (n e k : ℕ) : ℕ :=
  Nat.choose (n - 1) k + shiftedChoose (n - e - 1) 1 k

@[simp] theorem starBound_zero (n e : ℕ) : starBound n e 0 = 1 := by
  simp [starBound, shiftedChoose]

theorem starBound_succ (n e k : ℕ) :
    starBound n e (k + 1) = Nat.choose (n - 1) (k + 1) + Nat.choose (n - e - 1) k := by
  simp [starBound, shiftedChoose]

@[simp] theorem starBound_one (n e : ℕ) (hn : 0 < n) : starBound n e 1 = n := by
  rw [show 1 = 0 + 1 by rfl, starBound_succ]
  simp only [Nat.zero_add, Nat.choose_one_right, Nat.choose_zero_right]
  omega

/-- With no edges the comparison polynomial is the full subset polynomial. -/
theorem starBound_no_edges (n k : ℕ) (hn : 0 < n) : starBound n 0 k = Nat.choose n k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [starBound_succ]
    have hp := Nat.choose_succ_succ' (n - 1) k
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at hp
    simpa [Nat.add_comm] using hp.symm

/-- Deleting an isolated vertex corresponds exactly to multiplying by `1+X`. -/
theorem starBound_isolated_step (n e k : ℕ) (hn : 2 ≤ n) (he : e ≤ n - 2) :
    starBound (n - 1) e (k + 1) + starBound (n - 1) e k = starBound n e (k + 1) := by
  cases k with
  | zero =>
    rw [starBound_one _ _ (by omega), starBound_zero, starBound_one _ _ (by omega)]
    omega
  | succ k =>
    simp only [starBound_succ]
    have hn' : n - 1 - 1 = n - 2 := by omega
    have hn'' : n - 2 + 1 = n - 1 := by omega
    have he' : n - 1 - e - 1 + 1 = n - e - 1 := by omega
    have hp := Nat.choose_succ_succ' (n - 2) (k + 1)
    have hq := Nat.choose_succ_succ' (n - 1 - e - 1) k
    rw [hn''] at hp
    rw [he'] at hq
    rw [hn']
    omega

/-- At a leaf, the other deletion branch needs only the unrestricted subset
bound. Pascal's identity then recovers the comparison polynomial exactly. -/
theorem starBound_leaf_step (n e k : ℕ) (hn : 2 ≤ n) (he : 1 ≤ e) :
    starBound (n - 1) (e - 1) (k + 1) + Nat.choose (n - 2) k = starBound n e (k + 1) := by
  simp only [starBound_succ]
  have hn' : n - 1 - 1 = n - 2 := by omega
  have hn'' : n - 2 + 1 = n - 1 := by omega
  have he' : n - 1 - (e - 1) - 1 = n - e - 1 := by omega
  have hp := Nat.choose_succ_succ' (n - 2) k
  rw [hn''] at hp
  rw [hn', he']
  omega

variable {V : Type*} [DecidableEq V]

/-- Among forests with the same nonzero vertex count and the same edge count,
the star together with isolated vertices bounds every independence coefficient. -/
theorem countIndependent_le_starBound
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hS : S.Nonempty) (k : ℕ) :
    countIndependent G S k ≤ starBound S.card (edgeCountOn G S) k := by
  classical
  revert hS k
  refine Finset.strongInductionOn S ?_
  intro S ih hS k
  cases k with
  | zero => simp
  | succ k =>
    by_cases he0 : edgeCountOn G S = 0
    · rw [he0, starBound_no_edges S.card (k + 1) (card_pos.mpr hS)]
      exact countIndependent_le_choose G S (k + 1)
    have hePos : 1 ≤ edgeCountOn G S := by omega
    have heBound := edgeCountOn_add_one_le_card_of_isAcyclic G hG S hS
    have hn : 2 ≤ S.card := by omega
    obtain ⟨v, hv, hvLeaf⟩ := exists_closedNeighborhoodIn_card_le_two G hG S hS
    have hclosed := card_closedNeighborhoodIn_eq_degree_add_one G S hv
    have hdegree : (S.filter (G.Adj v)).card ≤ 1 := by omega
    have hcardDel : (S.erase v).card = S.card - 1 := card_erase_of_mem hv
    have hDelNonempty : (S.erase v).Nonempty := by
      apply card_pos.mp
      rw [hcardDel]
      omega
    have hDelEdge := edgeCountOn_erase_add_degree G S hv
    have hInd (q : ℕ) := ih (S.erase v) (erase_ssubset hv) hDelNonempty q
    by_cases hd0 : (S.filter (G.Adj v)).card = 0
    · have heDel : edgeCountOn G (S.erase v) = edgeCountOn G S := by omega
      have hshort := edgeCountOn_add_one_le_card_of_isAcyclic G hG (S.erase v) hDelNonempty
      have he : edgeCountOn G S ≤ S.card - 2 := by
        rw [hcardDel, heDel] at hshort
        omega
      calc
        countIndependent G S (k + 1) =
            countIndependent G (S.erase v) (k + 1) + countIndependent G (S.erase v) k := by
          rw [countIndependent_succ_delete_vertex G S hv k,
            sdiff_closedNeighborhoodIn_eq_erase_of_degree_zero G S hv hd0]
        _ ≤ starBound (S.erase v).card (edgeCountOn G (S.erase v)) (k + 1) +
            starBound (S.erase v).card (edgeCountOn G (S.erase v)) k :=
          Nat.add_le_add (hInd (k + 1)) (hInd k)
        _ = starBound S.card (edgeCountOn G S) (k + 1) := by
          rw [hcardDel, heDel]
          exact starBound_isolated_step S.card (edgeCountOn G S) k hn he
    · have hd1 : (S.filter (G.Adj v)).card = 1 := by omega
      have heDel : edgeCountOn G (S.erase v) = edgeCountOn G S - 1 := by omega
      have hc2 : (closedNeighborhoodIn G S v).card = 2 := by omega
      have hrestCard : (S \ closedNeighborhoodIn G S v).card = S.card - 2 := by
        rw [card_sdiff_closedNeighborhoodIn, hc2]
      calc
        countIndependent G S (k + 1) =
            countIndependent G (S.erase v) (k + 1) +
              countIndependent G (S \ closedNeighborhoodIn G S v) k :=
          countIndependent_succ_delete_vertex G S hv k
        _ ≤ starBound (S.erase v).card (edgeCountOn G (S.erase v)) (k + 1) +
            Nat.choose (S \ closedNeighborhoodIn G S v).card k :=
          Nat.add_le_add (hInd (k + 1))
            (countIndependent_le_choose G (S \ closedNeighborhoodIn G S v) k)
        _ = starBound S.card (edgeCountOn G S) (k + 1) := by
          rw [hcardDel, heDel, hrestCard]
          exact starBound_leaf_step S.card (edgeCountOn G S) k hn hePos

/-- The explicit guarded-binomial form used by the fixed-edge-count row. -/
theorem countIndependent_le_choose_add_shiftedChoose
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hS : S.Nonempty) (k : ℕ) :
    countIndependent G S k ≤ Nat.choose (S.card - 1) k +
      shiftedChoose (S.card - edgeCountOn G S - 1) 1 k :=
  countIndependent_le_starBound G hG S hS k

#print axioms starBound_isolated_step
#print axioms starBound_leaf_step
#print axioms countIndependent_le_starBound
#print axioms countIndependent_le_choose_add_shiftedChoose

end ForestUnimodality
