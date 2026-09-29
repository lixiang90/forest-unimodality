import ForestUnimodality.TerminalContextCertificate

/-! The path-context certificates use the opposite root state. Their path
premises cannot be silently changed from the actual host state. The other
state closes directly by endpoint arithmetic, so both actual states are
covered without that invalid substitution. -/
namespace ForestUnimodality.TerminalAlternateState
open TerminalBlockRecurrence

def endpointCheck : Bool := terminalLegs.all fun legs =>
  (List.range 24).all fun j =>
    let s := bridgeState legs (j + 1)
    decide (185 ≤ E s s.delta 0 0 1 ∧ 185 ≤ E s s.delta 0 0 3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem endpointCheck_eq_true : endpointCheck = true := by decide +kernel

theorem alternate_endpoints (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hblo : 1 ≤ b) (hbhi : b ≤ 24) :
    let s := bridgeState legs b
    185 ≤ E s s.delta 0 0 1 ∧ 185 ≤ E s s.delta 0 0 3 := by
  have h := List.all_eq_true.mp endpointCheck_eq_true legs hl
  have h := of_decide_eq_true (List.all_eq_true.mp h (b - 1)
    (List.mem_range.mpr (by omega)))
  simpa only [Nat.sub_add_cancel hblo] using h

theorem iterate_mass_pos (s : BlockState ℝ) (hA : 0 < s.A) (hB : 0 < s.B) (n : ℕ) :
    0 < (iterate n s).A ∧ 0 < (iterate n s).B := by
  induction n with
  | zero => exact ⟨hA, hB⟩
  | succ n ih =>
    change 0 < (iterate n s).A + (iterate n s).B ∧ 0 < 2 * (iterate n s).A
    exact ⟨add_pos ih.1 ih.2, mul_pos (by norm_num) ih.1⟩

/-- The matching state has a strictly positive residual before using any
path-context inequality. -/
theorem alternate_positive (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hblo : 1 ≤ b) (hbhi : b ≤ 24)
    (X Y r : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    let s := castState (bridgeState legs b)
    0 < E s s.delta X Y r := by
  obtain ⟨h1, h3⟩ := alternate_endpoints legs hl b hblo hbhi
  have h1' : (0 : ℝ) < E (castState (bridgeState legs b))
      (castState (bridgeState legs b)).delta 0 0 1 := by
    have hh : (0 : ℚ) < E (bridgeState legs b) (bridgeState legs b).delta 0 0 1 := by linarith
    have hh' : (0 : ℝ) < (E (bridgeState legs b) (bridgeState legs b).delta 0 0 1 : ℚ) :=
      by exact_mod_cast hh
    simpa only [cast_E, castState, Rat.cast_zero, Rat.cast_one] using hh'
  have h3' : (0 : ℝ) < E (castState (bridgeState legs b))
      (castState (bridgeState legs b)).delta 0 0 3 := by
    have hh : (0 : ℚ) < E (bridgeState legs b) (bridgeState legs b).delta 0 0 3 := by linarith
    have hh' : (0 : ℝ) < (E (bridgeState legs b) (bridgeState legs b).delta 0 0 3 : ℚ) :=
      by exact_mod_cast hh
    simpa only [cast_E, castState, Rat.cast_zero, Rat.cast_ofNat] using hh'
  have hp := affine_interpolation_positive
    (fun r => E (castState (bridgeState legs b))
      (castState (bridgeState legs b)).delta 0 0 r)
    (by intro t; unfold E; ring) h1' h3' hrlo hrhi
  obtain ⟨hA, hB, _⟩ := terminal_initial_bounds legs hl
  have hm := iterate_mass_pos _ hA hB (b - 1)
  rw [← cast_iterate] at hm
  change 0 < (castState (bridgeState legs b)).A ∧
    0 < (castState (bridgeState legs b)).B at hm
  have hx := mul_nonneg hm.1.le hX
  have hy := mul_nonneg hm.2.le hY
  dsimp only
  unfold E at hp ⊢
  nlinarith

/-- Both actual host states, with every path premise kept in that same
actual state. The two structural exceptions remain explicit. -/
theorem short_bridge_all_states_positive (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hblo : 1 ≤ b) (hbhi : b ≤ 24)
    (hne : ¬ (b = 1 ∧ (legs = [3,3] ∨ legs = [5,3])))
    (d X Y r : ℝ) (hd : d = 0 ∨ d = 1)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hrlo : 1 ≤ r) (hrhi : r ≤ 3)
    (hpath : ∀ j : ℕ, 0 < j → (j : ℝ) < (castState (bridgeState legs b)).N →
      0 ≤ E (castState (TerminalContextCertificate.pathState j)) d X Y r) :
    0 < E (castState (bridgeState legs b)) d X Y r := by
  by_cases he : d = (castState (bridgeState legs b)).delta
  · rw [he]
    exact alternate_positive legs hl b hblo hbhi X Y r hX hY hrlo hrhi
  · have ho : d = 1 - (castState (bridgeState legs b)).delta := by
      rcases hd with hd | hd <;>
        rcases bridge_binary_state legs hl b with hs | hs <;> simp_all
    rw [ho] at hpath ⊢
    exact TerminalContextCertificate.short_bridge_positive_real_state
      legs hl b hblo hbhi hne X Y r hX hY hrlo hrhi hpath

#print axioms endpointCheck_eq_true
#print axioms alternate_positive
#print axioms short_bridge_all_states_positive
end ForestUnimodality.TerminalAlternateState
