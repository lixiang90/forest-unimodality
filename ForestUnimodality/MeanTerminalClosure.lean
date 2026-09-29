import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Fin

/-!
Arithmetic closure of the scale-corrected activity-two mean argument.

These independently written proofs establish the unbounded branch-count
inequality. Graph decompositions and identification of actual rooted-tree
parameters are separate theorems: no exhaustion of forests is asserted here.
-/

namespace ForestUnimodality.MeanTerminalClosure

open Finset
open scoped BigOperators

/-- The explicit lower potential for a fan of at least six branches. -/
noncomputable def tailPotential (m : ℕ) : ℝ :=
  (7 / 5 : ℝ)^m * (343 * (m : ℝ) / 1140 - 89 / 60) -
    11 * (m : ℝ) / 30 + 89 / 60

theorem tailPotential_six : tailPotential 6 = 5068593 / 2968750 := by
  norm_num [tailPotential]

/-- Every successive increment after six is at least 11/60. This is a
universal induction step, not extrapolation from a bounded search. -/
theorem tailPotential_step (m : ℕ) (hm : 6 ≤ m) :
    11 / 60 ≤ tailPotential (m + 1) - tailPotential m := by
  have hmR : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (1 : ℝ) ≤ (7 / 5 : ℝ)^m := one_le_pow₀ (by norm_num)
  have hc : (11 / 20 : ℝ) ≤
      2 / 5 * (343 * (m : ℝ) / 1140 - 89 / 60) + 7 / 5 * (343 / 1140) := by
    linarith
  have heq : tailPotential (m + 1) - tailPotential m =
      (7 / 5 : ℝ)^m *
        (2 / 5 * (343 * (m : ℝ) / 1140 - 89 / 60) + 7 / 5 * (343 / 1140)) -
          11 / 30 := by
    simp only [tailPotential, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  rw [heq]
  nlinarith

theorem tailPotential_lower (m : ℕ) (hm : 6 ≤ m) :
    5068593 / 2968750 ≤ tailPotential m := by
  induction m, hm using Nat.le_induction with
  | base => rw [tailPotential_six]
  | succ m hm ih =>
    have hstep := tailPotential_step m hm
    linarith

theorem tailPotential_pos (m : ℕ) (hm : 6 ≤ m) : 0 < tailPotential m := by
  have h := tailPotential_lower m hm
  linarith

/-- The full arbitrary-size terminal-fan residual is positive from the three
uniform per-branch bounds and the actual leaf-host ratio interval. -/
theorem terminal_fan_positive {ι : Type*} (s : Finset ι)
    (R a b : ι → ℝ) (r : ℝ) (hm : 6 ≤ s.card)
    (hR : ∀ i ∈ s, 7 / 5 ≤ R i)
    (ha : ∀ i ∈ s, 343 / 1140 ≤ a i)
    (hb : ∀ i ∈ s, -(11 / 60) ≤ b i)
    (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3) :
    0 < (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 89 / 60) +
      (r - 1) * (∑ i ∈ s, b i) + 89 / 60 := by
  have hmR : (6 : ℝ) ≤ s.card := by exact_mod_cast hm
  have hprod : (7 / 5 : ℝ)^s.card ≤ ∏ i ∈ s, R i := by
    simpa only [prod_const] using
      prod_le_prod (fun i (_ : i ∈ s) => (by norm_num : (0 : ℝ) ≤ 7 / 5)) hR
  have hsumA : 343 * (s.card : ℝ) / 1140 ≤ ∑ i ∈ s, a i := by
    calc
      _ = ∑ _i ∈ s, (343 / 1140 : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum ha
  have hsumB : -(11 * (s.card : ℝ) / 60) ≤ ∑ i ∈ s, b i := by
    calc
      _ = ∑ _i ∈ s, -(11 / 60 : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum hb
  have hpos : 0 ≤ (∑ i ∈ s, a i) - 89 / 60 := by linarith
  have hmain : (7 / 5 : ℝ)^s.card * (343 * (s.card : ℝ) / 1140 - 89 / 60) ≤
      (∏ i ∈ s, R i) * ((∑ i ∈ s, a i) - 89 / 60) := by
    calc
      _ ≤ (7 / 5 : ℝ)^s.card * ((∑ i ∈ s, a i) - 89 / 60) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by norm_num) _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hpos
  have hcost : -(11 * (s.card : ℝ) / 30) ≤ (r - 1) * (∑ i ∈ s, b i) := by
    have hmul := mul_le_mul_of_nonneg_left hsumB (show 0 ≤ r - 1 by linarith)
    have hn : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have htail := tailPotential_pos s.card hm
  dsimp [tailPotential] at htail
  linarith

/-- Source parameter indices: 0=T33, 1=T35, then P2,P4,P6,P8,P10,P12.
These are rational parameter data, not definitions of graphs. -/
def branchRatio : ℕ → ℚ
  | 0 => 171 / 121 | 1 => 683 / 473 | 2 => 5 / 3 | 3 => 21 / 11
  | 4 => 85 / 43 | 5 => 341 / 171 | 6 => 1365 / 683 | 7 => 5461 / 2731
  | _ => 0

def branchExcess : ℕ → ℚ
  | 0 => 343 / 1140 | 1 => 4399 / 13660 | 2 => 13 / 30 | 3 => 67 / 105
  | 4 => 25 / 34 | 5 => 4042 / 5115 | 6 => 2267 / 2730 | 7 => 23641 / 27305
  | _ => 0

def branchDeletedExcess : ℕ → ℚ
  | 0 => 167 / 660 | 1 => 1789 / 9460 | 2 => 1 / 30 | 3 => -(19 / 165)
  | 4 => -(77 / 430) | 5 => -(52 / 285) | 6 => -(661 / 4098) | 7 => -(1799 / 13655)
  | _ => 0

theorem branch_parameter_bounds (i : ℕ) (hi : i < 8) :
    7 / 5 ≤ branchRatio i ∧ 343 / 1140 ≤ branchExcess i ∧
      -(11 / 60) ≤ branchDeletedExcess i := by
  interval_cases i <;> norm_num [branchRatio, branchExcess, branchDeletedExcess]

/-- Canonical nonincreasing fans, with each index strictly below `bound`.
The recursive bound proves enumeration exhaustiveness without trusting a
generated list or imposing any bound on the original forest. -/
def DescendingBounded : ℕ → List ℕ → Prop
  | _, [] => True
  | bound, i :: is => i < bound ∧ DescendingBounded (i + 1) is

def enumerateFans : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | m + 1, bound => (List.range bound).flatMap fun i =>
      (enumerateFans m (i + 1)).map (i :: ·)

theorem mem_enumerateFans (m bound : ℕ) (fan : List ℕ) :
    fan ∈ enumerateFans m bound ↔ fan.length = m ∧ DescendingBounded bound fan := by
  induction m generalizing bound fan with
  | zero =>
    cases fan <;> simp [enumerateFans, DescendingBounded]
  | succ m ih =>
    cases fan with
    | nil => simp [enumerateFans, DescendingBounded]
    | cons i is =>
      simp only [enumerateFans, List.mem_flatMap, List.mem_range, List.mem_map,
        List.cons.injEq, List.length_cons, DescendingBounded]
      constructor
      · rintro ⟨j, hj, rest, hrest, hji, hrestEq⟩
        subst j
        subst rest
        obtain ⟨hsize, hdesc⟩ := (ih (i + 1) is).mp hrest
        exact ⟨by omega, hj, hdesc⟩
      · rintro ⟨hsize, hib, hdesc⟩
        exact ⟨i, hib, is, (ih (i + 1) is).mpr ⟨by omega, hdesc⟩, rfl, rfl⟩

def hasTerminal (fan : List ℕ) : Bool := fan.any fun i => decide (i < 2)

/-- The affine host-ratio margin after eliminating the two-point-path row. -/
def fanMargin (fan : List ℕ) (r : ℚ) : ℚ :=
  60 * (fan.map branchRatio).prod * ((fan.map branchExcess).sum - 89 / 60) +
    60 * (r - 1) * (fan.map branchDeletedExcess).sum + 107 - 2 * r

def smallFanEndpointCheck (fan : List ℕ) : Bool :=
  if hasTerminal fan then
    decide (3523 / 473 ≤ fanMargin fan (5 / 3) ∧ 3523 / 473 ≤ fanMargin fan 3)
  else true

def smallFanCheck : Bool := ([2, 3, 4, 5] : List ℕ).all fun m =>
  (enumerateFans m 8).all smallFanEndpointCheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallFanCheck_eq_true : smallFanCheck = true := by
  decide +kernel

/-- The 823 actual rational endpoint checks, combined with a proved exhaustive
enumeration, cover every canonical fan of two through five listed branches
containing at least one terminal branch. -/
theorem small_fan_endpoint_margins (fan : List ℕ)
    (hlo : 2 ≤ fan.length) (hhi : fan.length ≤ 5)
    (hdesc : DescendingBounded 8 fan) (hterminal : hasTerminal fan = true) :
    3523 / 473 ≤ fanMargin fan (5 / 3) ∧ 3523 / 473 ≤ fanMargin fan 3 := by
  have hm : fan.length ∈ ([2, 3, 4, 5] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hall := List.all_eq_true.mp smallFanCheck_eq_true fan.length hm
  have hin := (mem_enumerateFans fan.length 8 fan).mpr ⟨rfl, hdesc⟩
  have hcheck := List.all_eq_true.mp hall fan hin
  simpa [smallFanEndpointCheck, hterminal] using hcheck

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_fan_terminal_count :
    ((([2, 3, 4, 5] : List ℕ).flatMap fun m => enumerateFans m 8).filter hasTerminal).length =
      823 := by
  decide +kernel

private theorem descendingBounded_of_pairwise (bound : ℕ) (fan : List ℕ)
    (hbound : ∀ i ∈ fan, i < bound) (hpair : fan.Pairwise (fun i j => j ≤ i)) :
    DescendingBounded bound fan := by
  induction fan generalizing bound with
  | nil => trivial
  | cons i is ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
    exact ⟨hbound i (by simp), ih (i + 1) (fun j hj => by
      have hji := hhead j hj
      omega) htail⟩

theorem fanMargin_perm {fan other : List ℕ} (h : fan.Perm other) (r : ℚ) :
    fanMargin fan r = fanMargin other r := by
  unfold fanMargin
  rw [(h.map branchRatio).prod_eq, (h.map branchExcess).sum_eq,
    (h.map branchDeletedExcess).sum_eq]

/-- The finite result does not require a caller to choose any particular
ordering of branches. Sorting is justified by permutation invariance. -/
theorem small_fan_endpoint_margins_unordered (fan : List ℕ)
    (hlo : 2 ≤ fan.length) (hhi : fan.length ≤ 5)
    (hbound : ∀ i ∈ fan, i < 8) (hterminal : hasTerminal fan = true) :
    3523 / 473 ≤ fanMargin fan (5 / 3) ∧ 3523 / 473 ≤ fanMargin fan 3 := by
  let ordered := fan.mergeSort (fun i j => decide (j ≤ i))
  have hp : ordered.Perm fan := List.mergeSort_perm _ _
  have hlen : ordered.length = fan.length := hp.length_eq
  have hdesc : DescendingBounded 8 ordered := descendingBounded_of_pairwise 8 ordered
    (fun i hi => hbound i (hp.mem_iff.mp hi)) (List.pairwise_mergeSort' _ fan)
  have hterm : hasTerminal ordered = true := by
    simp only [hasTerminal, List.any_eq_true, decide_eq_true_eq] at hterminal ⊢
    obtain ⟨i, hi, hit⟩ := hterminal
    exact ⟨i, hp.mem_iff.mpr hi, hit⟩
  have h := small_fan_endpoint_margins ordered (by omega) (by omega) hdesc hterm
  rwa [fanMargin_perm hp, fanMargin_perm hp] at h

/-- An affine function on the leaf-host ratio interval inherits the exact
common lower margin of its two endpoints. -/
theorem affine_host_margin (c d r L : ℝ) (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3)
    (hlo : L ≤ c + d * (5 / 3)) (hhi : L ≤ c + d * 3) : L ≤ c + d * r := by
  by_cases hd : 0 ≤ d
  · have h := mul_le_mul_of_nonneg_left hrlo hd
    linarith
  · have h := mul_le_mul_of_nonpos_left hrhi (le_of_not_ge hd)
    linarith

/-- All real host ratios are certified, not just the two rational endpoints. -/
theorem small_fan_margin_real (fan : List ℕ)
    (hlo : 2 ≤ fan.length) (hhi : fan.length ≤ 5)
    (hbound : ∀ i ∈ fan, i < 8) (hterminal : hasTerminal fan = true)
    (r : ℝ) (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3) :
    3523 / 473 ≤
      60 * ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) +
        60 * (r - 1) * ((fan.map branchDeletedExcess).sum : ℝ) + 107 - 2 * r := by
  obtain ⟨hleft, hright⟩ := small_fan_endpoint_margins_unordered fan hlo hhi hbound hterminal
  have hleftR : (3523 / 473 : ℝ) ≤ (fanMargin fan (5 / 3) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hleft
  have hrightR : (3523 / 473 : ℝ) ≤ (fanMargin fan 3 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hright
  simp only [fanMargin, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat] at hleftR hrightR
  have h := affine_host_margin
    (60 * ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) -
      60 * ((fan.map branchDeletedExcess).sum : ℝ) + 107)
    (60 * ((fan.map branchDeletedExcess).sum : ℝ) - 2) r (3523 / 473)
    hrlo hrhi (by nlinarith [hleftR]) (by nlinarith [hrightR])
  nlinarith

/-- Pure algebra of the common two-point-path elimination, with the variables
kept explicit so a graph attachment theorem can supply their actual values. -/
theorem terminal_elimination_identity (A R X Y r sa sb : ℝ) :
    60 * A * (X + (R - 1) * Y + R * (sa - 89 / 60) + (r - 1) * sb + 89 / 60) -
      A / 3 * (180 * X + 120 * Y + 6 * r - 54) =
    A * (60 * R - 100) * Y +
      A * (60 * R * (sa - 89 / 60) + 60 * (r - 1) * sb + 107 - 2 * r) := by
  ring

theorem branch_ratio_product_lower (fan : List ℕ) (hbound : ∀ i ∈ fan, i < 8) :
    (7 / 5 : ℚ)^fan.length ≤ (fan.map branchRatio).prod := by
  induction fan with
  | nil => simp
  | cons i is ih =>
    have hRi := (branch_parameter_bounds i (hbound i (by simp))).1
    have htail := ih (fun j hj => hbound j (by simp [hj]))
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    rw [mul_comm ((7 / 5 : ℚ)^is.length)]
    exact mul_le_mul hRi htail (pow_nonneg (by norm_num) _)
      (by linarith)

theorem branch_ratio_product_gt (fan : List ℕ) (hlo : 2 ≤ fan.length)
    (hbound : ∀ i ∈ fan, i < 8) :
    (5 / 3 : ℝ) < ((fan.map branchRatio).prod : ℝ) := by
  have hprod := branch_ratio_product_lower fan hbound
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 7 / 5) hlo
  have hq : (5 / 3 : ℚ) < (fan.map branchRatio).prod := by
    norm_num at hp
    linarith
  simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hq

/-- Complete scalar closure for two to five branches. The path constraint
replaces any need for an independent lower bound on X. -/
theorem small_fan_closure (fan : List ℕ)
    (hlo : 2 ≤ fan.length) (hhi : fan.length ≤ 5)
    (hbound : ∀ i ∈ fan, i < 8) (hterminal : hasTerminal fan = true)
    (A X Y r : ℝ) (hA : 0 < A) (hY : 0 ≤ Y)
    (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3)
    (hpath : 0 ≤ 180 * X + 120 * Y + 6 * r - 54) :
    0 < 60 * A *
      (X + (((fan.map branchRatio).prod : ℝ) - 1) * Y +
        ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) +
        (r - 1) * ((fan.map branchDeletedExcess).sum : ℝ) + 89 / 60) := by
  have hm := small_fan_margin_real fan hlo hhi hbound hterminal r hrlo hrhi
  have hR := branch_ratio_product_gt fan hlo hbound
  have heq := terminal_elimination_identity A ((fan.map branchRatio).prod : ℝ)
    X Y r ((fan.map branchExcess).sum : ℝ) ((fan.map branchDeletedExcess).sum : ℝ)
  have hfirst : 0 ≤ A * (60 * ((fan.map branchRatio).prod : ℝ) - 100) * Y :=
    mul_nonneg (mul_nonneg hA.le (by linarith)) hY
  have hsecond : 0 < A *
      (60 * ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) +
        60 * (r - 1) * ((fan.map branchDeletedExcess).sum : ℝ) + 107 - 2 * r) :=
    mul_pos hA (by linarith)
  have hpathMul : 0 ≤ A / 3 * (180 * X + 120 * Y + 6 * r - 54) :=
    mul_nonneg (by linarith) hpath
  linarith

private theorem cast_prod_map_index (fan : List ℕ) (f : ℕ → ℚ) :
    ((fan.map f).prod : ℝ) = ∏ i : Fin fan.length, (f fan[i] : ℝ) := by
  calc
    _ = (fan.map fun j => (f j : ℝ)).prod := by
      induction fan with
      | nil => simp
      | cons i is ih => simp only [List.map_cons, List.prod_cons, Rat.cast_mul, ih]
    _ = _ := by rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]; rfl

private theorem cast_sum_map_index (fan : List ℕ) (f : ℕ → ℚ) :
    ((fan.map f).sum : ℝ) = ∑ i : Fin fan.length, (f fan[i] : ℝ) := by
  calc
    _ = (fan.map fun j => (f j : ℝ)).sum := by
      induction fan with
      | nil => simp
      | cons i is ih => simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih]
    _ = _ := by rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]; rfl

theorem branch_parameter_bounds_real (i : ℕ) (hi : i < 8) :
    (7 / 5 : ℝ) ≤ (branchRatio i : ℝ) ∧
      (343 / 1140 : ℝ) ≤ (branchExcess i : ℝ) ∧
      -(11 / 60 : ℝ) ≤ (branchDeletedExcess i : ℝ) := by
  obtain ⟨hR, ha, hb⟩ := branch_parameter_bounds i hi
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hR
  constructor
  · simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr ha
  · simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hb

/-- The same actual parameter table closes every fan of at least six branches,
without needing a terminal-branch condition or a path auxiliary constraint. -/
theorem large_fan_residual_positive (fan : List ℕ) (hlo : 6 ≤ fan.length)
    (hbound : ∀ i ∈ fan, i < 8)
    (r : ℝ) (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3) :
    0 < ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) +
      (r - 1) * ((fan.map branchDeletedExcess).sum : ℝ) + 89 / 60 := by
  have hp (i : Fin fan.length) := branch_parameter_bounds_real fan[i]
    (hbound _ (List.getElem_mem _))
  have h := terminal_fan_positive (univ : Finset (Fin fan.length))
    (fun i => (branchRatio fan[i] : ℝ))
    (fun i => (branchExcess fan[i] : ℝ))
    (fun i => (branchDeletedExcess fan[i] : ℝ)) r
    (by simpa using hlo) (fun i _ => (hp i).1)
    (fun i _ => (hp i).2.1) (fun i _ => (hp i).2.2) hrlo hrhi
  simpa only [← cast_prod_map_index, ← cast_sum_map_index] using h

/-- Complete arithmetic closure for every finite number of the eight branch
types. No upper bound on the fan size or prescribed branch ordering remains. -/
theorem fan_closure (fan : List ℕ) (hlo : 2 ≤ fan.length)
    (hbound : ∀ i ∈ fan, i < 8) (hterminal : hasTerminal fan = true)
    (A X Y r : ℝ) (hA : 0 < A) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hrlo : 5 / 3 ≤ r) (hrhi : r ≤ 3)
    (hpath : 0 ≤ 180 * X + 120 * Y + 6 * r - 54) :
    0 < 60 * A *
      (X + (((fan.map branchRatio).prod : ℝ) - 1) * Y +
        ((fan.map branchRatio).prod : ℝ) * (((fan.map branchExcess).sum : ℝ) - 89 / 60) +
        (r - 1) * ((fan.map branchDeletedExcess).sum : ℝ) + 89 / 60) := by
  by_cases hsmall : fan.length ≤ 5
  · exact small_fan_closure fan hlo hsmall hbound hterminal A X Y r hA hY hrlo hrhi hpath
  · have hlarge : 6 ≤ fan.length := by omega
    have hres := large_fan_residual_positive fan hlarge hbound r hrlo hrhi
    have hR := branch_ratio_product_gt fan hlo hbound
    have hRY : 0 ≤ (((fan.map branchRatio).prod : ℝ) - 1) * Y :=
      mul_nonneg (by linarith) hY
    apply mul_pos (mul_pos (by norm_num) hA)
    linarith

#print axioms tailPotential_step
#print axioms terminal_fan_positive
#print axioms small_fan_endpoint_margins
#print axioms small_fan_margin_real
#print axioms small_fan_terminal_count
#print axioms terminal_elimination_identity
#print axioms small_fan_closure
#print axioms fan_closure

end ForestUnimodality.MeanTerminalClosure
