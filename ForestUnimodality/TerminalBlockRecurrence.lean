import ForestUnimodality.ShortLegFinite

/-! Algebra of a rooted terminal block and the unbounded bridge-length tail.
The fields are numerical statistics; identifying a real graph with a state
is deliberately a separate theorem. -/

namespace ForestUnimodality.TerminalBlockRecurrence

structure BlockState (R : Type*) where
  A : R
  B : R
  MA : R
  MB : R
  N : R
  alpha : R
  delta : R
  deriving DecidableEq

variable {R : Type*}

def extend [Ring R] (s : BlockState R) : BlockState R :=
  ⟨s.A + s.B, 2 * s.A, s.MA + s.MB, 2 * (s.MA + s.A),
    s.N + 1, s.alpha + 1 - s.delta, 1 - s.delta⟩

def iterate [Ring R] : ℕ → BlockState R → BlockState R
  | 0, s => s
  | n + 1, s => extend (iterate n s)

theorem iterate_add [Ring R] (m n : ℕ) (s : BlockState R) :
    iterate (m + n) s = iterate m (iterate n s) := by
  induction m with
  | zero => simp [iterate]
  | succ m ih => simp only [Nat.succ_add, iterate, ih]

def P [Ring R] (s : BlockState R) (r : R) : R := r * s.A + s.B

/-- Exact scaled affine attachment residual, with host state d. -/
def E [Ring R] (s : BlockState R) (d X Y r : R) : R :=
  let C := 60 * s.alpha - 60 * d * s.delta + 29 * s.N
  60 * s.A * X + 60 * s.B * Y + (180 * s.MA - C * s.A) * r +
    180 * s.MB - (C + 29 + 60 * d) * s.B

def residual [Ring R] (s : BlockState R) (r : R) : R := E s (1 - s.delta) 0 0 r

theorem extend_two_state [CommRing R] (s : BlockState R) :
    (iterate 2 s).N = s.N + 2 ∧ (iterate 2 s).alpha = s.alpha + 1 ∧
      (iterate 2 s).delta = s.delta := by
  simp only [iterate, extend]
  constructor
  · ring
  constructor <;> ring

theorem E_state_difference [CommRing R] (s : BlockState R) (X Y r : R) :
    E s 1 X Y r - E s 0 X Y r = 60 * (s.delta * P s r - s.B) := by
  unfold E P
  ring

theorem residual_worst_state (s : BlockState ℝ) (hA : 0 ≤ s.A) (hB : 0 ≤ s.B)
    (hs : s.delta = 0 ∨ s.delta = 1) (d r : ℝ)
    (hd : d = 0 ∨ d = 1) (hr : 0 ≤ r) : residual s r ≤ E s d 0 0 r := by
  rcases hs with hs | hs <;> rcases hd with rfl | rfl <;>
    simp only [residual, E, hs] <;> nlinarith [mul_nonneg hA hr]

theorem P_two [CommRing R] (s : BlockState R) (r : R) :
    P (iterate 2 s) r = (3 * r + 2) * s.A + (r + 2) * s.B := by
  simp only [P, iterate, extend]
  ring

theorem P_recurrence [CommRing R] (s : BlockState R) (r : R) :
    P (iterate 4 s) r = 5 * P (iterate 2 s) r - 4 * P s r := by
  simp only [P, iterate, extend]
  ring

set_option maxHeartbeats 800000 in
/-- The two-step inhomogeneous recurrence is an identity for every state. -/
theorem residual_recurrence [CommRing R] (s : BlockState R) (r : R) :
    residual (iterate 4 s) r = 5 * residual (iterate 2 s) r - 4 * residual s r +
      130 * P (iterate 2 s) r - 496 * P s r := by
  simp only [residual, E, P, iterate, extend]
  ring

/-- Homogeneous form of the rooted-message interval [2/3,6/5]. -/
def MessageCone (s : BlockState ℝ) : Prop :=
  0 < s.A ∧ 0 < s.B ∧ 2 * s.A ≤ 3 * s.B ∧ 5 * s.B ≤ 6 * s.A

theorem MessageCone.extend_stable {s : BlockState ℝ} (h : MessageCone s) :
    MessageCone (extend s) := by
  rcases h with ⟨hA, hB, hlo, hhi⟩
  simp only [MessageCone, extend]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem MessageCone.iterate_stable {s : BlockState ℝ} (h : MessageCone s) (n : ℕ) :
    MessageCone (iterate n s) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.extend_stable

theorem messageCone_after_two (s : BlockState ℝ) (hA : 0 < s.A) (hB : 0 < s.B)
    (hBA : s.B ≤ 2 * s.A) : MessageCone (iterate 2 s) := by
  simp only [MessageCone, iterate, extend]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem P_positive {s : BlockState ℝ} (h : MessageCone s) {r : ℝ} (hr : 1 ≤ r) :
    0 < P s r := by
  exact add_pos (mul_pos (by linarith) h.1) h.2.1

theorem P_growth {s : BlockState ℝ} (h : MessageCone s)
    {r : ℝ} (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    43 * P s r ≤ 11 * P (iterate 2 s) r := by
  have h1 := mul_nonneg (sub_nonneg.mpr hrhi) (sub_nonneg.mpr h.2.2.2)
  have h2 := mul_nonneg (sub_nonneg.mpr hrlo) (sub_nonneg.mpr h.2.2.1)
  rw [P_two]
  unfold P
  nlinarith

theorem forcing_positive {s : BlockState ℝ} (h : MessageCone s)
    {r : ℝ} (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < 130 * P (iterate 2 s) r - 496 * P s r := by
  have hp := P_positive h hrlo
  have hg := P_growth h hrlo hrhi
  nlinarith

/-- Two positive starting residuals with a positive increment propagate
through every subsequent bridge length of the same parity. -/
theorem residual_even_tail (s : BlockState ℝ) (hs : MessageCone s)
    (r : ℝ) (hrlo : 1 ≤ r) (hrhi : r ≤ 3)
    (h0 : 0 < residual s r) (h2 : residual s r < residual (iterate 2 s) r)
    (m : ℕ) :
    0 < residual (iterate (2 * m) s) r ∧
      residual (iterate (2 * m) s) r < residual (iterate (2 * m + 2) s) r := by
  induction m with
  | zero => simpa only [mul_zero, zero_add, iterate] using And.intro h0 h2
  | succ m ih =>
    have hf := forcing_positive (hs.iterate_stable (2 * m)) hrlo hrhi
    have he := residual_recurrence (iterate (2 * m) s) r
    rw [← iterate_add, ← iterate_add] at he
    rw [← iterate_add] at hf
    have e2 : 2 + 2 * m = 2 * m + 2 := by omega
    have e4 : 4 + 2 * m = 2 * m + 4 := by omega
    rw [e2, e4] at he
    rw [e2] at hf
    rw [show 2 * (m + 1) = 2 * m + 2 by omega,
      show 2 * m + 2 + 2 = 2 * m + 4 by omega]
    exact ⟨lt_trans ih.1 ih.2, by linarith⟩

def terminalLegs : List (List ℕ) :=
  [[2,2]] ++ (MeanTerminalClosure.enumerateFans 2 7).map (ShortLegData.legsOf true) ++
    ShortLegData.oddTriples

/-- The bridge-one rooted cluster: the new root is the common leg center. -/
def terminalState (legs : List ℕ) : BlockState ℚ :=
  let A := (legs.map fun n => (ShortLegData.pathData n).1).prod
  let B := 2 * (legs.map fun n => (ShortLegData.pathData n).2.2.1).prod
  let a0 : ℕ := (legs.map fun n => (n + 1) / 2).sum
  let a1 : ℕ := 1 + (legs.map fun n => n / 2).sum
  let alpha : ℕ := max a0 a1
  ⟨A, B, A * (legs.map fun n => (ShortLegData.pathData n).2.1 /
      (ShortLegData.pathData n).1).sum,
    B * (1 + (legs.map fun n => (ShortLegData.pathData n).2.2.2 /
      (ShortLegData.pathData n).2.2.1).sum),
    ((1 + legs.sum : ℕ) : ℚ), (alpha : ℚ), ((alpha - a0 : ℕ) : ℚ)⟩

def bridgeState (legs : List ℕ) (b : ℕ) : BlockState ℚ := iterate (b - 1) (terminalState legs)

def castState (s : BlockState ℚ) : BlockState ℝ :=
  ⟨s.A, s.B, s.MA, s.MB, s.N, s.alpha, s.delta⟩

theorem cast_extend (s : BlockState ℚ) : castState (extend s) = extend (castState s) := by
  simp [castState, extend, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]

theorem cast_iterate (n : ℕ) (s : BlockState ℚ) :
    castState (iterate n s) = iterate n (castState s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, cast_extend, ih, iterate]

theorem cast_E (s : BlockState ℚ) (d X Y r : ℚ) :
    ((E s d X Y r : ℚ) : ℝ) = E (castState s) d X Y r := by
  simp [E, castState, Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat]

theorem cast_residual (s : BlockState ℚ) (r : ℚ) :
    ((residual s r : ℚ) : ℝ) = residual (castState s) r := by
  simp [residual, cast_E, castState, Rat.cast_sub, Rat.cast_one]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem terminalLegs_length : terminalLegs.length = 45 := by decide +kernel

def tailBaseCheck : Bool := terminalLegs.all fun legs =>
  ([25,26] : List ℕ).all fun b =>
    ([1,3] : List ℚ).all fun r =>
      decide (0 < residual (bridgeState legs b) r ∧
        residual (bridgeState legs b) r < residual (bridgeState legs (b + 2)) r)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tailBaseCheck_eq_true : tailBaseCheck = true := by decide +kernel

def initialMessageCheck : Bool := terminalLegs.all fun legs =>
  let s := terminalState legs
  decide (0 < s.A ∧ 0 < s.B ∧ s.B ≤ 2 * s.A ∧ (s.delta = 0 ∨ s.delta = 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem initialMessageCheck_eq_true : initialMessageCheck = true := by decide +kernel

theorem terminal_initial_bounds (legs : List ℕ) (hl : legs ∈ terminalLegs) :
    0 < (castState (terminalState legs)).A ∧
    0 < (castState (terminalState legs)).B ∧
    (castState (terminalState legs)).B ≤ 2 * (castState (terminalState legs)).A := by
  have h := of_decide_eq_true (List.all_eq_true.mp initialMessageCheck_eq_true legs hl)
  change 0 < (terminalState legs).A ∧ 0 < (terminalState legs).B ∧
    (terminalState legs).B ≤ 2 * (terminalState legs).A ∧ _ at h
  dsimp only [castState]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1⟩

theorem bridge_message_cone (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : 3 ≤ b) : MessageCone (castState (bridgeState legs b)) := by
  obtain ⟨hA, hB, hBA⟩ := terminal_initial_bounds legs hl
  have h := (messageCone_after_two _ hA hB hBA).iterate_stable (b - 3)
  rw [← iterate_add] at h
  have he : b - 3 + 2 = b - 1 := by omega
  rw [he] at h
  simpa only [bridgeState, cast_iterate] using h

theorem terminal_base_endpoints (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : b = 25 ∨ b = 26) (r : ℚ) (hr : r = 1 ∨ r = 3) :
    0 < residual (bridgeState legs b) r ∧
      residual (bridgeState legs b) r < residual (bridgeState legs (b + 2)) r := by
  have h := List.all_eq_true.mp tailBaseCheck_eq_true legs hl
  have h := List.all_eq_true.mp h b (by simpa using hb)
  exact of_decide_eq_true (List.all_eq_true.mp h r (by simpa using hr))

theorem affine_interpolation_positive (f : ℝ → ℝ)
    (hf : ∀ r, 2 * f r = (3 - r) * f 1 + (r - 1) * f 3)
    (h1 : 0 < f 1) (h3 : 0 < f 3) {r : ℝ} (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < f r := by
  by_cases hr : r = 1
  · simpa only [hr] using h1
  · have hr' : 1 < r := lt_of_le_of_ne hrlo (Ne.symm hr)
    have hp := mul_pos (show 0 < r - 1 by linarith) h3
    have hn := mul_nonneg (sub_nonneg.mpr hrhi) h1.le
    have he := hf r
    linarith

theorem residual_interpolation (s : BlockState ℝ) (r : ℝ) :
    2 * residual s r = (3 - r) * residual s 1 + (r - 1) * residual s 3 := by
  unfold residual E
  ring

theorem terminal_base_real (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : b = 25 ∨ b = 26) (r : ℝ) (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < residual (castState (bridgeState legs b)) r ∧
      residual (castState (bridgeState legs b)) r <
        residual (castState (bridgeState legs (b + 2))) r := by
  have h1 := terminal_base_endpoints legs hl b hb 1 (Or.inl rfl)
  have h3 := terminal_base_endpoints legs hl b hb 3 (Or.inr rfl)
  have h1' : 0 < residual (castState (bridgeState legs b)) 1 ∧
      0 < residual (castState (bridgeState legs (b + 2))) 1 -
        residual (castState (bridgeState legs b)) 1 := by
    have hcast : (0 : ℝ) < ((residual (bridgeState legs b) (1 : ℚ) : ℚ) : ℝ) ∧
        ((residual (bridgeState legs b) (1 : ℚ) : ℚ) : ℝ) <
          ((residual (bridgeState legs (b + 2)) (1 : ℚ) : ℚ) : ℝ) := by exact_mod_cast h1
    simpa only [cast_residual, Rat.cast_one, sub_pos] using hcast
  have h3' : 0 < residual (castState (bridgeState legs b)) 3 ∧
      0 < residual (castState (bridgeState legs (b + 2))) 3 -
        residual (castState (bridgeState legs b)) 3 := by
    have hcast : (0 : ℝ) < ((residual (bridgeState legs b) (3 : ℚ) : ℚ) : ℝ) ∧
        ((residual (bridgeState legs b) (3 : ℚ) : ℚ) : ℝ) <
          ((residual (bridgeState legs (b + 2)) (3 : ℚ) : ℚ) : ℝ) := by exact_mod_cast h3
    simpa only [cast_residual, Rat.cast_ofNat, sub_pos] using hcast
  refine ⟨affine_interpolation_positive _ (residual_interpolation _) h1'.1 h3'.1 hrlo hrhi, ?_⟩
  apply sub_pos.mp
  apply affine_interpolation_positive
    (fun x => residual (castState (bridgeState legs (b + 2))) x -
      residual (castState (bridgeState legs b)) x) _ h1'.2 h3'.2 hrlo hrhi
  intro x
  have he1 := residual_interpolation (castState (bridgeState legs (b + 2))) x
  have he2 := residual_interpolation (castState (bridgeState legs b)) x
  nlinarith

theorem bridgeState_add (legs : List ℕ) (b m : ℕ) (hb : 1 ≤ b) :
    bridgeState legs (b + m) = iterate m (bridgeState legs b) := by
  unfold bridgeState
  rw [show b + m - 1 = m + (b - 1) by omega, iterate_add]

/-- The 180 checked endpoints and the algebraic recurrence imply strict
positivity for every real host ratio and every bridge length b >= 25. -/
theorem long_bridge_positive (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : 25 ≤ b) (r : ℝ) (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < residual (castState (bridgeState legs b)) r := by
  let base := if (b - 25) % 2 = 0 then 25 else 26
  have hbase : base = 25 ∨ base = 26 := by unfold base; split_ifs <;> simp
  have hdecomp : base + 2 * ((b - 25) / 2) = b := by
    have hmod := Nat.mod_lt (b - 25) (by omega : 0 < 2)
    have hdiv := Nat.mod_add_div (b - 25) 2
    unfold base
    split_ifs <;> omega
  obtain ⟨h0, h2⟩ := terminal_base_real legs hl base hbase r hrlo hrhi
  have hcone := bridge_message_cone legs hl base (by omega)
  have h2' : residual (castState (bridgeState legs base)) r <
      residual (iterate 2 (castState (bridgeState legs base))) r := by
    rw [bridgeState_add legs base 2 (by omega), cast_iterate] at h2
    exact h2
  have h := (residual_even_tail _ hcone r hrlo hrhi h0 h2' ((b - 25) / 2)).1
  rw [← cast_iterate, ← bridgeState_add legs base _ (by omega), hdecomp] at h
  exact h

/-- Nonnegative host potentials add to the strictly positive long-bridge residual. -/
theorem long_bridge_affine_positive (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : 25 ≤ b) (X Y r : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < E (castState (bridgeState legs b))
      (1 - (castState (bridgeState legs b)).delta) X Y r := by
  have h := long_bridge_positive legs hl b hb r hrlo hrhi
  have hc := bridge_message_cone legs hl b (by omega)
  have hx := mul_nonneg hc.1.le hX
  have hy := mul_nonneg hc.2.1.le hY
  unfold residual E at h
  unfold E
  nlinarith

theorem iterate_binary_state [Ring R] (s : BlockState R)
    (hs : s.delta = 0 ∨ s.delta = 1) (n : ℕ) :
    (iterate n s).delta = 0 ∨ (iterate n s).delta = 1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    change 1 - (iterate n s).delta = 0 ∨ 1 - (iterate n s).delta = 1
    rcases ih with h | h <;> simp [h]

theorem bridge_binary_state (legs : List ℕ) (hl : legs ∈ terminalLegs) (b : ℕ) :
    (castState (bridgeState legs b)).delta = 0 ∨
      (castState (bridgeState legs b)).delta = 1 := by
  have h := of_decide_eq_true (List.all_eq_true.mp initialMessageCheck_eq_true legs hl)
  change _ ∧ _ ∧ _ ∧ ((terminalState legs).delta = 0 ∨ (terminalState legs).delta = 1) at h
  have hi := iterate_binary_state (terminalState legs) h.2.2.2 (b - 1)
  change ((bridgeState legs b).delta : ℝ) = 0 ∨ ((bridgeState legs b).delta : ℝ) = 1
  rcases hi with hi | hi <;> simp only [bridgeState, hi, Rat.cast_zero, Rat.cast_one, or_true, true_or]

/-- Long bridges close for either actual binary host state: the checked
opposite state is the worse one, so no state-selection premise is required. -/
theorem long_bridge_all_states_positive (legs : List ℕ) (hl : legs ∈ terminalLegs)
    (b : ℕ) (hb : 25 ≤ b) (d X Y r : ℝ) (hd : d = 0 ∨ d = 1)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hrlo : 1 ≤ r) (hrhi : r ≤ 3) :
    0 < E (castState (bridgeState legs b)) d X Y r := by
  have hp := long_bridge_positive legs hl b hb r hrlo hrhi
  have hc := bridge_message_cone legs hl b (by omega)
  have hw := residual_worst_state _ hc.1.le hc.2.1.le
    (bridge_binary_state legs hl b) d r hd (by linarith)
  have hx := mul_nonneg hc.1.le hX
  have hy := mul_nonneg hc.2.1.le hY
  have h0 := lt_of_lt_of_le hp hw
  unfold E at h0 ⊢
  nlinarith

theorem tailBaseCheck_count : terminalLegs.length * 2 * 2 = 180 := by
  rw [terminalLegs_length]

#print axioms residual_recurrence
#print axioms messageCone_after_two
#print axioms forcing_positive
#print axioms residual_even_tail
#print axioms terminalLegs_length
#print axioms tailBaseCheck_eq_true
#print axioms initialMessageCheck_eq_true
#print axioms long_bridge_positive
#print axioms long_bridge_affine_positive
#print axioms long_bridge_all_states_positive

end ForestUnimodality.TerminalBlockRecurrence
