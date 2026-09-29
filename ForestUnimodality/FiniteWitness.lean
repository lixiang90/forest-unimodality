import ForestUnimodality.IntegerCertificate
import ForestUnimodality.RowSoundness
import ForestUnimodality.DirectCriteria
import ForestUnimodality.Edgeless
import ForestUnimodality.SmallOrder

/-! Executable finite witnesses and their complete graph interpretation.
Coverage of the finite parameter domain remains an explicit data-check input. -/
namespace ForestUnimodality
namespace FiniteRows

inductive Witness where
  | rising
  | falling
  | linear (kind : Kind) (cert : Certificate)
  deriving Repr

/-- Check direct inequalities by exact natural arithmetic, or validate every
integer row and residual of a linear certificate. -/
def Witness.check (w : Witness) (n a k : ℕ) : Bool :=
  match w with
  | .rising => decide (matchingUpperCount a (n - a) (k - 1) < (n + 1 - k).choose k)
  | .falling => decide (matchingUpperCount a (n - a) (k + 1) ≤ (n + 1 - k).choose k)
  | .linear kind cert => cert.check n a k kind

/-- All finite parameters that can require a pre-tail certificate. -/
def Domain (n a k : ℕ) : Prop :=
  2 ≤ n ∧ n ≤ 60 ∧ (n + 1) / 2 ≤ a ∧ a < n ∧ 1 ≤ k ∧ k < (2 * a + 1) / 3

instance (n a k : ℕ) : Decidable (Domain n a k) := by
  unfold Domain
  infer_instance

variable {V : Type*} [DecidableEq V]

/-- Any accepted witness proves an actual graph alternative. The linear
conditional kind is interpreted with its implication premise intact. -/
theorem Witness.graph_alternative (w : Witness)
    {G : SimpleGraph V} {S I : Finset V}
    (hmin : IsEdgeMinimalMaximumOn G S I) (hG : G.IsAcyclic)
    (hav : (S \ I).card ≤ I.card) (hv : 1 ≤ (S \ I).card)
    (k : ℕ) (hk : 1 ≤ k) (hcheck : w.check S.card I.card k = true) :
    CertificateAlternative (countIndependent G S) k := by
  cases w with
  | rising =>
    apply Or.inl
    apply hmin.1.countIndependent_rising_of_direct_bound hG k
    exact of_decide_eq_true hcheck
  | falling =>
    apply Or.inr
    apply Or.inl
    apply hmin.1.countIndependent_falling_of_direct_bound hG k
    exact of_decide_eq_true hcheck
  | linear kind cert =>
    apply cert.graph_alternative hmin.1 hav hv k hk kind hcheck
    intro hconditional i
    exact rowHolds_of_valid hmin hG k hk kind cert.rows[i].row
      (cert.row_valid_of_check S.card I.card k kind hcheck i) hconditional

/-- Complete bounded-forest assembly from actual checked coverage. Small and
edgeless induced graphs are discharged by independent structural theorems. -/
theorem countIndependent_unimodal_of_domain_witnesses
    (hcoverage : ∀ n a k, Domain n a k → ∃ w : Witness, w.check n a k = true)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : S.card ≤ 60) :
    WeaklyUnimodal (countIndependent G S) := by
  classical
  by_cases hsmall : S.card ≤ 7
  · exact countIndependent_unimodal_of_isAcyclic_card_le_seven G hG S hsmall
  by_cases hind : G.IsIndepSet (S : Set V)
  · exact countIndependent_unimodal_of_indep G S hind
  obtain ⟨I, hmin⟩ := exists_edgeMinimalMaximumOn G S
  have hI := hmin.1
  have hhalf := hI.card_le_two_mul_of_isAcyclic hG
  have hsub := Finset.card_le_card hI.subset
  have hlt := hI.card_lt_of_not_indep hind
  have hdiff := Finset.card_sdiff_of_subset hI.subset
  have hav : (S \ I).card ≤ I.card := by omega
  have hv : 1 ≤ (S \ I).card := by omega
  apply countIndependent_unimodal_of_certificate_alternatives G hG S I hI
  intro k hk htail
  have hdomain : Domain S.card I.card k := by
    unfold Domain
    exact ⟨by omega, hn, by omega, hlt, hk, htail⟩
  obtain ⟨w, hw⟩ := hcoverage S.card I.card k hdomain
  exact w.graph_alternative hmin hG hav hv k hk hw

/-- The bounded result in the exact count vocabulary of the complete target. -/
theorem independentCount_unimodal_of_domain_witnesses
    (hcoverage : ∀ n a k, Domain n a k → ∃ w : Witness, w.check n a k = true)
    {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic) (hn : n ≤ 60) :
    WeaklyUnimodal (independentCount G) := by
  classical
  have h := countIndependent_unimodal_of_domain_witnesses hcoverage G hG Finset.univ
    (by simpa using hn)
  simpa only [WeaklyUnimodal, countIndependent_univ_eq_independentCount] using h

#print axioms Witness.graph_alternative
#print axioms countIndependent_unimodal_of_domain_witnesses
#print axioms independentCount_unimodal_of_domain_witnesses
end FiniteRows
end ForestUnimodality
