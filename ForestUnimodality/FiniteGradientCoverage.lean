import ForestUnimodality.FiniteGradientData.N01
import ForestUnimodality.FiniteGradientData.N02
import ForestUnimodality.FiniteGradientData.N03
import ForestUnimodality.FiniteGradientData.N04
import ForestUnimodality.FiniteGradientData.N05
import ForestUnimodality.FiniteGradientData.N06
import ForestUnimodality.FiniteGradientData.N07
import ForestUnimodality.FiniteGradientData.N08
import ForestUnimodality.FiniteGradientData.N09
import ForestUnimodality.FiniteGradientData.N10
import ForestUnimodality.FiniteGradientData.N11
import ForestUnimodality.FiniteGradientData.N12
import ForestUnimodality.FiniteGradientData.N13
import ForestUnimodality.FiniteGradientData.N14
import ForestUnimodality.FiniteGradientData.N15
import ForestUnimodality.FiniteGradientData.N16
import ForestUnimodality.FiniteGradientData.N17
import ForestUnimodality.FiniteGradientData.N18
import ForestUnimodality.FiniteGradientData.N19
import ForestUnimodality.FiniteGradientData.N20

namespace ForestUnimodality.FiniteGradientCoverage

theorem bound_nat (n j : ℕ) (hn : 1 ≤ n) (hn20 : n ≤ 20) (hj : j ≤ n)
    {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(n:ℝ)*q-j| * binomialMass n j q ≤ 31/100 := by
  interval_cases n
  · simpa using FiniteGradientData.N01.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N02.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N03.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N04.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N05.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N06.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N07.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N08.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N09.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N10.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N11.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N12.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N13.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N14.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N15.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N16.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N17.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N18.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N19.bound ⟨j, by omega⟩ hq
  · simpa using FiniteGradientData.N20.bound ⟨j, by omega⟩ hq

theorem bound (n : ℕ) (j : ℤ) (hn : 1 ≤ n) (hn20 : n ≤ 20)
    {q : ℝ} (hq : q ∈ Set.Icc (3/10:ℝ) (7/10)) :
    |(n:ℝ)*q-j| * binomialMass n j q ≤ 31/100 := by
  by_cases hj0 : 0 ≤ j
  · by_cases hjn : j ≤ n
    · lift j to ℕ using hj0
      have hj : j ≤ n := by exact_mod_cast hjn
      simpa only [Int.cast_natCast] using bound_nat n j hn hn20 hj hq
    · rw [binomialMass_eq_zero_of_gt n (lt_of_not_ge hjn), mul_zero]
      norm_num
  · rw [binomialMass_eq_zero_of_neg n (lt_of_not_ge hj0), mul_zero]
    norm_num

#print axioms bound
end ForestUnimodality.FiniteGradientCoverage
