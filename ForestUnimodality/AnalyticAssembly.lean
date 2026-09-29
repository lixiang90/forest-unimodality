import ForestUnimodality.Statement

/-! Pure sequence assembly for the analytic route. These lemmas make no claim
that a forest satisfies the rising-prefix, falling-tail, or central hypotheses.
Flat portions of the initial nondecreasing prefix are allowed. -/

namespace ForestUnimodality

/-- A unimodal suffix following a nondecreasing prefix gives a unimodal whole
sequence, including the step joining the prefix to the suffix. -/
theorem weaklyUnimodal_of_shift (f : ℕ → ℕ) (L : ℕ)
    (hbefore : ∀ k < L, f k ≤ f (k + 1))
    (hshift : WeaklyUnimodal (fun t => f (L + t))) : WeaklyUnimodal f := by
  obtain ⟨p, hrise, hfall⟩ := hshift
  refine ⟨L + p, ?_, ?_⟩
  · intro k hk
    by_cases hkL : k < L
    · exact hbefore k hkL
    · have hkp : k - L < p := by omega
      have h := hrise (k - L) hkp
      have heq : L + (k - L) = k := by omega
      simpa only [← Nat.add_assoc, heq] using h
  · intro k hk
    have hkp : p ≤ k - L := by omega
    have h := hfall (k - L) hkp
    have heq : L + (k - L) = k := by omega
    simpa only [← Nat.add_assoc, heq] using h

/-- A rising prefix, falling tail, and exclusion of weak valleys in between
imply weak unimodality. No claim of global no-recovery is needed: the prefix
may contain a flat step followed by a later increase. -/
theorem weaklyUnimodal_of_no_central_weak_valley (f : ℕ → ℕ) (L U : ℕ)
    (hbefore : ∀ k < L, f k ≤ f (k + 1))
    (hafter : ∀ k, U ≤ k → f (k + 1) ≤ f k)
    (hcentral : ∀ k, L ≤ k → k < U → 1 ≤ k →
      ¬ (f k ≤ f (k - 1) ∧ f k ≤ f (k + 1))) : WeaklyUnimodal f := by
  apply weaklyUnimodal_of_shift f L hbefore
  apply unimodal_of_no_recovery
  · refine ⟨U, ?_⟩
    simpa only [Nat.add_assoc] using hafter (L + U) (by omega)
  · intro t hstep
    by_cases htail : U ≤ L + (t + 1)
    · simpa only [Nat.add_assoc] using hafter (L + (t + 1)) htail
    · have hc := hcentral (L + (t + 1)) (by omega) (by omega) (by omega)
      have hprev : f (L + (t + 1)) ≤ f (L + (t + 1) - 1) := by
        have heq : L + (t + 1) - 1 = L + t := by omega
        rw [heq]
        exact hstep
      have hnot : ¬ f (L + (t + 1)) ≤ f (L + (t + 1) + 1) :=
        fun hnext => hc ⟨hprev, hnext⟩
      have h := le_of_lt (lt_of_not_ge hnot)
      simpa only [Nat.add_assoc] using h

/-- Equivalent convenient central input: after any nonincreasing central
step, the next step is strictly decreasing. -/
theorem weaklyUnimodal_of_central_strict_descent (f : ℕ → ℕ) (L U : ℕ)
    (hbefore : ∀ k < L, f k ≤ f (k + 1))
    (hafter : ∀ k, U ≤ k → f (k + 1) ≤ f k)
    (hcentral : ∀ k, L ≤ k → k < U → 1 ≤ k →
      f k ≤ f (k - 1) → f (k + 1) < f k) : WeaklyUnimodal f := by
  apply weaklyUnimodal_of_no_central_weak_valley f L U hbefore hafter
  intro k hkL hkU hkpos hvalley
  exact (not_lt_of_ge hvalley.2) (hcentral k hkL hkU hkpos hvalley.1)

#print axioms weaklyUnimodal_of_shift
#print axioms weaklyUnimodal_of_no_central_weak_valley
#print axioms weaklyUnimodal_of_central_strict_descent

end ForestUnimodality
