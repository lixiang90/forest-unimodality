import ForestUnimodality.FiniteMarginalSupport
import ForestUnimodality.HardCoreActivityWindow

/-! Reconstruct the entire feasible graph-order/rank list from necessary
inequalities. No witness-supplied list of pairs is trusted for completeness. -/
namespace ForestUnimodality.FiniteMarginalSupport

structure Parameters where
  lowerOrder : ℕ
  cap : ℕ
  lowerRank : ℕ
  upperRank : ℕ
  density : ℚ
  probabilityCap : ℚ
  deriving Repr

def Parameters.pairCheck (p : Parameters) (nk : ℕ × ℕ) : Bool := decide
  (p.lowerOrder ≤ nk.1 ∧ nk.1 ≤ p.cap ∧ p.lowerRank ≤ nk.2 ∧ nk.2 ≤ p.upperRank ∧
    nk.1 ≤ 4 * nk.2 ∧ 2 * nk.2 ≤ nk.1 ∧
    p.density * nk.1 ≤ (nk.2 : ℚ) ∧ (nk.2 : ℚ) ≤ p.probabilityCap * nk.1)

def Parameters.pairs (p : Parameters) : List (ℕ × ℕ) :=
  ((List.range (p.cap + 1)).product (List.range (p.cap + 1))).filter p.pairCheck

theorem Parameters.mem_pairs (p : Parameters) {n k : ℕ}
    (hn : n ≤ p.cap) (hk : k ≤ p.cap) (hcheck : p.pairCheck (n,k) = true) :
    (n,k) ∈ p.pairs := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_product.mpr ⟨?_, ?_⟩, hcheck⟩
  · exact List.mem_range.mpr (by omega)
  · exact List.mem_range.mpr (by omega)

variable {V : Type*} [DecidableEq V]

theorem Parameters.actual_mem_pairs (p : Parameters)
    (G : SimpleGraph V) (S : Finset V) {z : ℝ} (hz : 0 < z) (k : ℕ)
    (hmean : hardCoreMean G S z = k)
    (hnlo : p.lowerOrder ≤ S.card) (hnhi : S.card ≤ p.cap)
    (hklo : p.lowerRank ≤ k) (hkhi : k ≤ p.upperRank)
    (hrank : (S.card : ℝ) / 4 ≤ hardCoreMean G S z)
    (hhalf : 2 * k ≤ S.card)
    (hdensity : (p.density : ℝ) * S.card ≤ hardCoreMean G S z)
    (hq : z / (1 + z) ≤ (p.probabilityCap : ℝ)) :
    (S.card,k) ∈ p.pairs := by
  apply p.mem_pairs hnhi (by omega)
  apply decide_eq_true
  have hquarterR : (S.card : ℝ) ≤ 4 * (k : ℝ) := by linarith
  have hquarter : S.card ≤ 4 * k := by exact_mod_cast hquarterR
  have hdR : (p.density : ℝ) * S.card ≤ (k : ℝ) := by simpa only [hmean] using hdensity
  have hdQ : p.density * S.card ≤ (k : ℚ) := by exact_mod_cast hdR
  have hm := hardCoreMean_le_card_mul_activity G S hz.le
  have hqm := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg S.card : (0 : ℝ) ≤ _)
  have hupperR : (k : ℝ) ≤ (p.probabilityCap : ℝ) * S.card := by
    rw [hmean] at hm
    calc
      (k : ℝ) ≤ (S.card : ℝ) * (z / (1 + z)) := by simpa only [mul_div_assoc] using hm
      _ ≤ (S.card : ℝ) * (p.probabilityCap : ℝ) := hqm
      _ = _ := mul_comm _ _
  have hupperQ : (k : ℚ) ≤ p.probabilityCap * S.card := by exact_mod_cast hupperR
  exact ⟨hnlo, hnhi, hklo, hkhi, hquarter, hhalf, hdQ, hupperQ⟩

theorem integer_rank_lower {lo k : ℕ} {x : ℝ}
    (hx : x ≤ (k : ℝ)) (hgap : (lo : ℝ) - 1 < x) : lo ≤ k := by
  by_contra h
  have hk : k + 1 ≤ lo := by omega
  have hkR : (k : ℝ) + 1 ≤ lo := by exact_mod_cast hk
  linarith

theorem integer_rank_upper {hi k : ℕ} {x : ℝ}
    (hx : (k : ℝ) ≤ x) (hgap : x < (hi : ℝ) + 1) : k ≤ hi := by
  by_contra h
  have hk : hi + 1 ≤ k := by omega
  have hkR : (hi : ℝ) + 1 ≤ k := by exact_mod_cast hk
  linarith

theorem central_rank_half {n h k : ℕ} (hh : h ≤ n)
    (hk : k < (n + 2 * h) / 6 + 1) : 2 * k ≤ n := by omega

#print axioms Parameters.actual_mem_pairs
#print axioms central_rank_half
end ForestUnimodality.FiniteMarginalSupport
