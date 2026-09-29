import ForestUnimodality.GraphBounds
import ForestUnimodality.MaximumIndependent

/-!
Graphs whose maximum independent subset has at most two vertices have a
unimodal independence sequence. This includes empty ambient vertex sets and
does not require an acyclicity assumption.
-/

namespace ForestUnimodality

open Finset

/-- A nonnegative sequence supported in degrees zero through two is unimodal
when its first step is nondecreasing. -/
theorem weaklyUnimodal_of_support_le_two (f : ℕ → ℕ)
    (h01 : f 0 ≤ f 1) (hsupport : ∀ k, 2 < k → f k = 0) :
    WeaklyUnimodal f := by
  by_cases h12 : f 1 ≤ f 2
  · refine ⟨2, ?_, ?_⟩
    · intro k hk
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · exact h01
      · exact h12
    · intro k hk
      rw [hsupport (k + 1) (by omega)]
      exact Nat.zero_le _
  · refine ⟨1, ?_, ?_⟩
    · intro k hk
      have hk' : k = 0 := by omega
      subst k
      exact h01
    · intro k hk
      by_cases hk' : k = 1
      · subst k
        exact le_of_lt (lt_of_not_ge h12)
      · rw [hsupport (k + 1) (by omega)]
        exact Nat.zero_le _

variable {V : Type*} [DecidableEq V]

/-- No independent subset can have cardinality above that of a maximum one. -/
theorem IsMaximumIndependentOn.countIndependent_eq_zero_of_card_lt
    {G : SimpleGraph V} {S I : Finset V}
    (hI : IsMaximumIndependentOn G S I) {k : ℕ} (hk : I.card < k) :
    countIndependent G S k = 0 := by
  classical
  unfold countIndependent
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro J hJ hcard
  have hbound := hI.2 J hJ
  omega

/-- The empty ambient set has the sequence `1, 0, 0, ...`, with peak zero. -/
theorem countIndependent_empty_unimodal (G : SimpleGraph V) :
    WeaklyUnimodal (countIndependent G ∅) := by
  refine ⟨0, ?_, ?_⟩
  · intro k hk
    omega
  · intro k _
    rw [countIndependent_eq_zero_of_gt G ∅ (by simp)]
    exact Nat.zero_le _

/-- Every graph with maximum independent-set size at most two has a unimodal
independence sequence on its finite ambient vertex set. -/
theorem countIndependent_unimodal_of_maximum_card_le_two
    (G : SimpleGraph V) (S I : Finset V) (hI : IsMaximumIndependentOn G S I)
    (hsmall : I.card ≤ 2) : WeaklyUnimodal (countIndependent G S) := by
  by_cases hS : S.Nonempty
  · apply weaklyUnimodal_of_support_le_two
    · simpa using Finset.card_pos.mpr hS
    · intro k hk
      exact hI.countIndependent_eq_zero_of_card_lt (lt_of_le_of_lt hsmall hk)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hEmpty]
    exact countIndependent_empty_unimodal G

/-- The same result stated as a bound on every independent subset, without
requiring a particular maximum independent subset to be supplied. -/
theorem countIndependent_unimodal_of_independence_bound
    (G : SimpleGraph V) (S : Finset V)
    (hsmall : ∀ J ∈ independentSubsets G S, J.card ≤ 2) :
    WeaklyUnimodal (countIndependent G S) := by
  obtain ⟨I, hI⟩ := exists_maximumIndependentOn G S
  exact countIndependent_unimodal_of_maximum_card_le_two G S I hI (hsmall I hI.1)

/-- The small-independence theorem expressed in the full target's vocabulary. -/
theorem independentCount_unimodal_of_maximum_card_le_two {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n))
    (hI : IsMaximumIndependentOn G Finset.univ I) (hsmall : I.card ≤ 2) :
    WeaklyUnimodal (independentCount G) := by
  simpa only [WeaklyUnimodal, countIndependent_univ_eq_independentCount] using
    countIndependent_unimodal_of_maximum_card_le_two G Finset.univ I hI hsmall

#print axioms weaklyUnimodal_of_support_le_two
#print axioms IsMaximumIndependentOn.countIndependent_eq_zero_of_card_lt
#print axioms countIndependent_empty_unimodal
#print axioms countIndependent_unimodal_of_maximum_card_le_two
#print axioms countIndependent_unimodal_of_independence_bound
#print axioms independentCount_unimodal_of_maximum_card_le_two

end ForestUnimodality
