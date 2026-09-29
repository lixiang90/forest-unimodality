import ForestUnimodality.PathLowerBound
import ForestUnimodality.MatchingUpperBound

/-! Exact numerical comparisons of the path lower and matching upper bounds
imply the source manuscript's two direct certificate alternatives. -/

namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

theorem IsMaximumIndependentOn.countIndependent_rising_of_direct_bound
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (k : ℕ)
    (hcompare : matchingUpperCount I.card (S.card - I.card) (k - 1) <
      Nat.choose (S.card + 1 - k) k) :
    countIndependent G S (k - 1) < countIndependent G S k :=
  lt_of_le_of_lt (hI.countIndependent_le_matchingUpperCount_of_isAcyclic hG (k - 1))
    (lt_of_lt_of_le hcompare (choose_path_le_countIndependent G hG S k))

theorem IsMaximumIndependentOn.countIndependent_falling_of_direct_bound
    {G : SimpleGraph V} {S I : Finset V} (hI : IsMaximumIndependentOn G S I)
    (hG : G.IsAcyclic) (k : ℕ)
    (hcompare : matchingUpperCount I.card (S.card - I.card) (k + 1) ≤
      Nat.choose (S.card + 1 - k) k) :
    countIndependent G S (k + 1) ≤ countIndependent G S k :=
  (hI.countIndependent_le_matchingUpperCount_of_isAcyclic hG (k + 1)).trans
    (hcompare.trans (choose_path_le_countIndependent G hG S k))

#print axioms IsMaximumIndependentOn.countIndependent_rising_of_direct_bound
#print axioms IsMaximumIndependentOn.countIndependent_falling_of_direct_bound
end ForestUnimodality
