import ForestUnimodality.FiniteKernelGraphBudget

/-! Graph soundness for the final finite stage: fixed integer shifts carry
their own joint-count charges, and kernel checks need only cover states
proved to contain every positive-weight conditional configuration. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate
open Finset FiniteKernelCurvatureCertificate

noncomputable def RationalRow.graphBudgetWithCounts {ι : Type*} (r : RationalRow ι)
    (rate : ι → ℝ) (bound : ℤ → ℝ) (α β D m : ℝ) : ℝ :=
  KernelBudget.budget r.terms r.fixedIndices r.A r.B r.dδ r.dM α β D
    (fun i => (r.price i : ℝ)) rate (fun j => (r.fixedPrice j : ℝ)) bound m

theorem RationalRow.fixed_sum {ι : Type*} (r : RationalRow ι) (j : ℤ) (x : ℝ) :
    (∑ s ∈ r.fixedIndices, (r.fixedPrice s : ℝ) * (if j = s then x else 0)) =
      (r.fixed j : ℝ) * x := by
  classical
  by_cases hj : j ∈ r.fixedIndices
  · rw [sum_eq_single j]
    · simp [fixed, hj]
    · intro s _ hs
      simp [Ne.symm hs]
    · exact fun h => False.elim (h hj)
  · have hzero : (∑ s ∈ r.fixedIndices, (r.fixedPrice s : ℝ) * (if j = s then x else 0)) = 0 := by
      apply sum_eq_zero
      intro s hs
      have hjs : j ≠ s := by rintro rfl; exact hj hs
      simp [hjs]
    rw [hzero]
    simp [fixed, hj]

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem RationalRow.supportBudget_le_averaged (r : RationalRow ι) (w : IntervalWitness)
    (hr : r.signCheck = true) (N : ℕ) (support : ℕ → ℤ → Prop)
    (hcertificate : ∀ m ≤ N, ∀ j : ℤ, support m j →
      ∀ q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ), 0 ≤ r.toReal.residual m j q)
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    (hN : S.card ≤ N) {z : ℝ} (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ))
    (k : ℕ) (hmean : hardCoreMean G S z = k)
    (hsupport : ∀ y ∈ range ((S \ I).card + 1), ∀ m ∈ range (I.card + 1),
      0 < hardCoreLayerWeight G S I z y m → support m ((k : ℤ) - y))
    (α β D : ℝ) (rate : ι → ℝ) (bound : ℤ → ℝ)
    (hvarK : hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + α) * hardCoreAvailableMean G S I z + β)
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * hardCoreAvailableMean G S I z)
    (hlap : ∀ i ∈ r.terms, hardCoreLayerLaplace G S I z (r.retention i) ≤
      Real.exp (-rate i * hardCoreAvailableMean G S I z))
    (hcount : ∀ j ∈ r.fixedIndices, hardCoreFixedShiftMass G S I z k j ≤ bound j) :
    r.graphBudgetWithCounts rate bound α β D (hardCoreAvailableMean G S I z) ≤
      (r.scale : ℝ) * averagedBinomialKernel G S I z r.wL r.wR r.wC k := by
  have hs := of_decide_eq_true hr
  apply averagedBinomialKernel_budget_lower G S I hIS hI hz k hmean r.terms r.fixedIndices
    r.wL r.wR r.wC r.scale r.A r.B r.C r.dδ r.dM α β D
    (fun i => (r.price i : ℝ)) (fun i => (r.retention i : ℝ)) rate
    (fun j => (r.fixedPrice j : ℝ)) bound
  · exact_mod_cast hs.1.2.2.2.2.1
  · exact_mod_cast hs.1.2.2.2.2.2
  · intro i hi
    exact_mod_cast (hs.2.1 i hi).1
  · intro j hj
    exact_mod_cast hs.2.2 j hj
  · exact hvarK
  · exact hvarM
  · exact hlap
  · exact hcount
  · intro y hy m hm hw
    have hmI : m ≤ I.card := by simpa only [mem_range, Nat.lt_add_one_iff] using hm
    have hmN := hmI.trans ((card_le_card hIS).trans hN)
    have hp := r.toReal.pointwise_lower_of_residual_nonneg m ((k : ℤ) - y)
      (z / (1 + z)) (hcertificate m hmN _ (hsupport y hy m hm hw) _ hq)
    simp only [toReal, Int.cast_sub, Int.cast_natCast] at hp
    rw [r.fixed_sum]
    have hδ : (k : ℝ) - y - z / (1 + z) * m = (k : ℝ) - binomialLayerMean y m z := by
      unfold binomialLayerMean
      ring
    simpa only [hδ] using hp

theorem RationalRow.averaged_pos_of_supportBudget (r : RationalRow ι)
    (hr : r.signCheck = true) (G : SimpleGraph V) (S I : Finset V) (z : ℝ) (k : ℕ)
    (α β D : ℝ) (rate : ι → ℝ) (bound : ℤ → ℝ)
    (hbound : r.graphBudgetWithCounts rate bound α β D (hardCoreAvailableMean G S I z) ≤
      (r.scale : ℝ) * averagedBinomialKernel G S I z r.wL r.wR r.wC k)
    (hbudget : 0 < r.graphBudgetWithCounts rate bound α β D (hardCoreAvailableMean G S I z)) :
    0 < averagedBinomialKernel G S I z r.wL r.wR r.wC k := by
  have hs := of_decide_eq_true hr
  have hscale : (0 : ℝ) < r.scale := by exact_mod_cast hs.1.1
  exact (mul_pos_iff_of_pos_left hscale).mp (hbudget.trans_le hbound)

#print axioms RationalRow.fixed_sum
#print axioms RationalRow.supportBudget_le_averaged
#print axioms RationalRow.averaged_pos_of_supportBudget
end ForestUnimodality.FiniteKernelRationalCertificate
