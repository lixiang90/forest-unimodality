import ForestUnimodality.NegativePowerHermite
import ForestUnimodality.LowerTailCharges

/-! Negative-power prices averaged over the actual hard-core layer law.
Real cutoffs, the variance, and every cumulative tail refer to the same law. -/
namespace ForestUnimodality.NegativePowerLayerBudget

open Finset
open NegativePowerHermite

variable {V : Type*} [DecidableEq V]

theorem layer_add (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    (f g : ℕ → ℕ → ℝ) :
    hardCoreLayerExpectation G S I z (fun j M => f j M + g j M) =
      hardCoreLayerExpectation G S I z f + hardCoreLayerExpectation G S I z g := by
  simp only [hardCoreLayerExpectation_eq_expect, KernelBudget.expect_add]

theorem layer_sub (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    (f g : ℕ → ℕ → ℝ) :
    hardCoreLayerExpectation G S I z (fun j M => f j M - g j M) =
      hardCoreLayerExpectation G S I z f - hardCoreLayerExpectation G S I z g := by
  simp only [hardCoreLayerExpectation_eq_expect, KernelBudget.expect_sub]

theorem layer_const_mul (G : SimpleGraph V) (S I : Finset V) (z c : ℝ)
    (f : ℕ → ℕ → ℝ) :
    hardCoreLayerExpectation G S I z (fun j M => c * f j M) =
      c * hardCoreLayerExpectation G S I z f := by
  simp only [hardCoreLayerExpectation_eq_expect, KernelBudget.expect_const_mul]

theorem layer_const (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 ≤ z) (c : ℝ) :
    hardCoreLayerExpectation G S I z (fun _ _ => c) = c := by
  unfold hardCoreLayerExpectation
  simp only [← sum_mul, sum_hardCoreLayerWeight G S I hIS hI hz, one_mul]

theorem layer_sum (G : SimpleGraph V) (S I : Finset V) (z : ℝ)
    (t : Finset ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    hardCoreLayerExpectation G S I z (fun j M => ∑ i ∈ t, f i j M) =
      ∑ i ∈ t, hardCoreLayerExpectation G S I z (f i) := by
  simp only [hardCoreLayerExpectation_eq_expect, KernelBudget.expect_sum]

theorem layer_mono (G : SimpleGraph V) (S I : Finset V) {z : ℝ} (hz : 0 ≤ z)
    (f g : ℕ → ℕ → ℝ) (hfg : ∀ j M, f j M ≤ g j M) :
    hardCoreLayerExpectation G S I z f ≤ hardCoreLayerExpectation G S I z g := by
  unfold hardCoreLayerExpectation
  exact sum_le_sum fun j _ => sum_le_sum fun M _ =>
    mul_le_mul_of_nonneg_left (hfg j M) (hardCoreLayerWeight_nonneg G S I hz j M)

theorem layer_envelope_eq (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m : ℝ} (hz : 0 ≤ z)
    (hm : m = hardCoreAvailableMean G S I z) (hm0 : m ≠ 0) (p beta : ℝ) :
    hardCoreLayerExpectation G S I z (fun _ M => envelope p beta ((M : ℝ) / m)) =
      1 + coefficient p beta / m ^ 2 * hardCoreAvailableVariance G S I z := by
  have hmean : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ)) = m := by
    simpa only [hardCoreLayerExpectation, hardCoreAvailableMean] using hm.symm
  have hcenter : hardCoreLayerExpectation G S I z (fun _ M => (M : ℝ) - m) = 0 := by
    rw [layer_sub, hmean, layer_const G S I hIS hI hz]
    ring
  have hpoint (M : ℕ) : envelope p beta ((M : ℝ) / m) =
      1 - (p / m) * ((M : ℝ) - m) +
        (coefficient p beta / m ^ 2) * ((M : ℝ) - m) ^ 2 := by
    unfold envelope
    field_simp
  simp_rw [hpoint]
  rw [layer_add, layer_sub, layer_const G S I hIS hI hz,
    layer_const_mul, layer_const_mul, hcenter, mul_zero, sub_zero]
  rw [hm]
  rfl

theorem layer_envelope_le (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m p beta D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hp : 0 < p) (hb : 0 < beta) (hb1 : beta < 1)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m) :
    hardCoreLayerExpectation G S I z (fun _ M => envelope p beta ((M : ℝ) / m)) ≤
      1 + coefficient p beta * D / m := by
  rw [layer_envelope_eq G S I hIS hI hz hm hm0.ne' p beta]
  have hB : 0 ≤ coefficient p beta := by
    exact (by positivity : 0 ≤ p * (p + 1) / 2).trans (coefficient_lower hp hb hb1)
  have he : coefficient p beta / m ^ 2 * (D * m) = coefficient p beta * D / m := by
    field_simp
  calc
    _ ≤ 1 + coefficient p beta / m ^ 2 * (D * m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hvar (div_nonneg hB (sq_nonneg m)))
    _ = _ := by rw [he]

theorem exists_cut_interval (cuts : ℕ → ℝ) (n : ℕ) {y : ℝ}
    (hlo : cuts 0 ≤ y) (hhi : y < cuts (n + 1)) :
    ∃ i ≤ n, cuts i ≤ y ∧ y < cuts (i + 1) := by
  induction n with
  | zero => exact ⟨0, le_rfl, hlo, hhi⟩
  | succ n ih =>
    by_cases h : y < cuts (n + 1)
    · obtain ⟨i, hi, hlo, hhi⟩ := ih h
      exact ⟨i, hi.trans (Nat.le_succ n), hlo, hhi⟩
    · exact ⟨n + 1, le_rfl, le_of_not_gt h, hhi⟩

theorem cut_le_of_steps (cuts : ℕ → ℝ) (n : ℕ)
    (hsteps : ∀ i ≤ n, cuts i ≤ cuts (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n + 1) : cuts i ≤ cuts j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (hsteps j (by omega))

theorem truncated_le_envelope_slices {p alpha beta : ℝ}
    (hp : 0 < p) (ha : 0 < alpha) (hab : alpha < beta) (hb1 : beta < 1)
    (cuts U : ℕ → ℝ) (n : ℕ) (hstart : cuts 0 = alpha) (hend : cuts (n + 1) = beta)
    (hsteps : ∀ i ≤ n, cuts i ≤ cuts (i + 1))
    (hU : ∀ i ≤ n, positiveGap p beta (cuts i) ≤ U i) (y : ℝ) :
    (if alpha ≤ y then y ^ (-p) else 0) ≤ envelope p beta y +
      ∑ i ∈ range (n + 1), U i * (if cuts i ≤ y ∧ y < cuts (i + 1) then 1 else 0) := by
  have hb : 0 < beta := ha.trans hab
  have hUn (i : ℕ) (hi : i ≤ n) : 0 ≤ U i :=
    (le_max_left _ _).trans (hU i hi)
  have hterm (i : ℕ) (hi : i ∈ range (n + 1)) :
      0 ≤ U i * (if cuts i ≤ y ∧ y < cuts (i + 1) then 1 else 0) := by
    exact mul_nonneg (hUn i (by simpa using mem_range.mp hi)) (by split_ifs <;> norm_num)
  have hsum := sum_nonneg hterm
  by_cases hay : alpha ≤ y
  · simp only [if_pos hay]
    by_cases hby : beta ≤ y
    · exact (rpow_le_envelope hp hb hb1 hby).trans (le_add_of_nonneg_right hsum)
    · have hyb : y < beta := lt_of_not_ge hby
      obtain ⟨i, hi, hiy, hyi⟩ := exists_cut_interval cuts n
        (hstart ▸ hay) (hend ▸ hyb)
      have hc0 : 0 < cuts i := ha.trans_le (hstart ▸
        cut_le_of_steps cuts n hsteps (Nat.zero_le i) (by omega))
      have hcβ : cuts i ≤ beta := hend ▸
        cut_le_of_steps cuts n hsteps (by omega) le_rfl
      have hg : positiveGap p beta y ≤ U i :=
        (positiveGap_antitone hp hb hb1 ⟨hc0, hcβ⟩ ⟨ha.trans_le hay, hyb.le⟩ hiy).trans
          (hU i hi)
      have his : U i ≤ ∑ j ∈ range (n + 1),
          U j * (if cuts j ≤ y ∧ y < cuts (j + 1) then 1 else 0) := by
        simpa only [if_pos (And.intro hiy hyi), mul_one] using
          single_le_sum hterm (mem_range.mpr (by omega : i < n + 1))
      have hgap : y ^ (-p) - envelope p beta y ≤ positiveGap p beta y := le_max_right _ _
      linarith
  · simp only [if_neg hay]
    exact add_nonneg (envelope_pos hp hb hb1 y).le hsum

/-- The old single Hermite bound, valid for every positive exponent,
including the exponent 7/2 of the triangular-kernel error. -/
theorem single_hermite_layer_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m p alpha D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hp : 0 < p) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m) :
    hardCoreLayerExpectation G S I z
      (fun _ M => if alpha * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-p) else 0) ≤
        1 + coefficient p alpha * D / m := by
  apply (layer_mono G S I hz _ _ ?_).trans (layer_envelope_le G S I hIS hI hz hm hm0
    hp ha ha1 hvar)
  intro j M
  by_cases h : alpha * m ≤ (M : ℝ)
  · simp only [if_pos h]
    exact rpow_le_envelope hp ha ha1 ((le_div_iff₀ hm0).mpr h)
  · simp only [if_neg h]
    exact (envelope_pos hp ha ha1 _).le

/-- Stage-350 equation (3.1). The cutoffs are real; all tail bounds and
moments are those of this same hard-core layer distribution. -/
theorem sliced_hermite_layer_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m p alpha beta D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hp : 0 < p) (ha : 0 < alpha) (hab : alpha < beta) (hb1 : beta < 1)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m)
    (cuts U rate : ℕ → ℝ) (n : ℕ)
    (hstart : cuts 0 = alpha) (hend : cuts (n + 1) = beta)
    (hsteps : ∀ i ≤ n, cuts i ≤ cuts (i + 1))
    (hU : ∀ i ≤ n, positiveGap p beta (cuts i) ≤ U i)
    (hUdec : ∀ i < n, U (i + 1) ≤ U i) (hUlast : U (n + 1) = 0)
    (htail : ∀ i ≤ n, hardCoreAvailableLowerTail G S I z (cuts (i + 1) * m) ≤
      Real.exp (-m * rate i)) :
    hardCoreLayerExpectation G S I z
      (fun _ M => if alpha * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-p) else 0) ≤
        1 + coefficient p beta * D / m +
          ∑ i ∈ range (n + 1), (U i - U (i + 1)) * Real.exp (-m * rate i) := by
  have hUn (i : ℕ) (hi : i ≤ n) : 0 ≤ U i :=
    (le_max_left _ _).trans (hU i hi)
  have hpoint (j M : ℕ) :
      (if alpha * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-p) else 0) ≤
        envelope p beta ((M : ℝ) / m) +
          ∑ i ∈ range (n + 1), U i *
            (if cuts i * m ≤ (M : ℝ) ∧ (M : ℝ) < cuts (i + 1) * m then 1 else 0) := by
    simpa only [le_div_iff₀ hm0, div_lt_iff₀ hm0] using
      truncated_le_envelope_slices hp ha hab hb1 cuts U n hstart hend hsteps hU ((M : ℝ) / m)
  have he := layer_mono G S I hz _ _ hpoint
  simp only [layer_add, layer_sum, layer_const_mul] at he
  have hc := hardCoreAvailableSlices_le_cumulative G S I hz (fun i => cuts i * m)
    U (fun i => Real.exp (-m * rate (i - 1))) n
    (fun i hi => mul_le_mul_of_nonneg_right (hsteps i hi) hm0.le)
    (hUn 0 (Nat.zero_le n)) (hUn n le_rfl) hUdec
    (fun i hi => by simpa using htail i hi)
  simp only [Nat.add_sub_cancel] at hc
  have hcost : U n * Real.exp (-m * rate n) +
      (∑ i ∈ range n, (U i - U (i + 1)) * Real.exp (-m * rate i)) =
      ∑ i ∈ range (n + 1), (U i - U (i + 1)) * Real.exp (-m * rate i) := by
    rw [sum_range_succ, hUlast, sub_zero]
    ring
  rw [hcost] at hc
  have hquad := layer_envelope_le G S I hIS hI hz hm hm0 hp (ha.trans hab) hb1 hvar
  change _ ≤ hardCoreLayerExpectation G S I z (fun _ M => envelope p beta ((M : ℝ) / m)) +
    ∑ i ∈ range (n + 1), U i * hardCoreAvailableSlice G S I z
      (cuts i * m) (cuts (i + 1) * m) at he
  exact he.trans (add_le_add hquad hc)

/-- Choosing the prices as the actual endpoint gaps discharges both the
pointwise price check and their decreasing order analytically. -/
theorem sliced_hermite_exact_gap_layer_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m p alpha beta D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (hp : 0 < p) (ha : 0 < alpha) (hab : alpha < beta) (hb1 : beta < 1)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m)
    (cuts rate : ℕ → ℝ) (n : ℕ)
    (hstart : cuts 0 = alpha) (hend : cuts (n + 1) = beta)
    (hsteps : ∀ i ≤ n, cuts i ≤ cuts (i + 1))
    (htail : ∀ i ≤ n, hardCoreAvailableLowerTail G S I z (cuts (i + 1) * m) ≤
      Real.exp (-m * rate i)) :
    hardCoreLayerExpectation G S I z
      (fun _ M => if alpha * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-p) else 0) ≤
        1 + coefficient p beta * D / m +
          ∑ i ∈ range (n + 1),
            (positiveGap p beta (cuts i) - positiveGap p beta (cuts (i + 1))) *
              Real.exp (-m * rate i) := by
  apply sliced_hermite_layer_bound G S I hIS hI hz hm hm0 hp ha hab hb1 hvar
    cuts (fun i => positiveGap p beta (cuts i)) rate n hstart hend hsteps
    (fun _ _ => le_rfl) ?_ ?_ htail
  · intro i hi
    have hmem (j : ℕ) (hj : j ≤ n + 1) : cuts j ∈ Set.Icc alpha beta := by
      constructor
      · rw [← hstart]
        exact cut_le_of_steps cuts n hsteps (Nat.zero_le j) hj
      · rw [← hend]
        exact cut_le_of_steps cuts n hsteps hj le_rfl
    exact positiveGap_antitoneOn_interval hp ha hab hb1
      (hmem i (by omega)) (hmem (i + 1) (by omega)) (hsteps i (by omega))
  · rw [hend]
    exact positiveGap_zero_of_ge hp (ha.trans hab) hb1 le_rfl

theorem seventh_half_layer_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z m alpha D : ℝ}
    (hz : 0 ≤ z) (hm : m = hardCoreAvailableMean G S I z) (hm0 : 0 < m)
    (ha : 0 < alpha) (ha1 : alpha < 1)
    (hvar : hardCoreAvailableVariance G S I z ≤ D * m) :
    hardCoreLayerExpectation G S I z
      (fun _ M => if alpha * m ≤ (M : ℝ) then ((M : ℝ) / m) ^ (-(7 / 2 : ℝ)) else 0) ≤
        1 + coefficient (7 / 2) alpha * D / m :=
  single_hermite_layer_bound G S I hIS hI hz hm hm0 (by norm_num) ha ha1 hvar

#print axioms layer_envelope_eq
#print axioms single_hermite_layer_bound
#print axioms sliced_hermite_layer_bound
#print axioms sliced_hermite_exact_gap_layer_bound
#print axioms seventh_half_layer_bound

end ForestUnimodality.NegativePowerLayerBudget
