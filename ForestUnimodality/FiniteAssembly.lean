import ForestUnimodality.ForestTail

/-! The finite certificate alternatives imply unimodality once the proven
forest tail begins. The alternatives remain explicit unproved inputs here. -/

namespace ForestUnimodality
variable {V : Type*} [DecidableEq V]

/-- The three allowed certificate conclusions at the source paper's index k.
In particular the third alternative preserves its nonpositive-step premise. -/
def CertificateAlternative (f : ℕ → ℕ) (k : ℕ) : Prop :=
  f (k - 1) < f k ∨ f (k + 1) ≤ f k ∨
    (f k ≤ f (k - 1) → f (k + 1) ≤ f k)

/-- All required pre-tail certificate signs imply the full sequence statement.
No finite certificate coverage is claimed by this assembly theorem. -/
theorem countIndependent_unimodal_of_certificate_alternatives
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S I : Finset V)
    (hI : IsMaximumIndependentOn G S I)
    (hcert : ∀ k, 1 ≤ k → k < (2 * I.card + 1) / 3 →
      CertificateAlternative (countIndependent G S) k) :
    WeaklyUnimodal (countIndependent G S) := by
  apply unimodal_of_no_recovery
  · exact ⟨(2 * I.card + 1) / 3,
      hI.countIndependent_succ_le_of_cutoff hG _ (le_refl _)⟩
  · intro k hstep
    by_cases htail : (2 * I.card + 1) / 3 ≤ k + 1
    · simpa only [Nat.add_assoc] using
        hI.countIndependent_succ_le_of_cutoff hG (k + 1) htail
    · have hc := hcert (k + 1) (by omega) (by omega)
      simp only [CertificateAlternative, Nat.add_sub_cancel, Nat.add_assoc] at hc
      rcases hc with hpos | hneg | hcond
      · exact (not_lt_of_ge hstep hpos).elim
      · exact hneg
      · exact hcond hstep

#print axioms countIndependent_unimodal_of_certificate_alternatives
end ForestUnimodality
