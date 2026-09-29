import ForestUnimodality.FiniteKernelRationalCertificate
import ForestUnimodality.KernelBudget

/-! The finite degree domain is connected to the actual conditional forest
mixture by cardinality. The probability space is unchanged when the row is
averaged. The remaining source and scalar budget obligations stay explicit. -/
namespace ForestUnimodality.FiniteKernelRationalCertificate

open Finset FiniteKernelCurvatureCertificate

noncomputable def RationalRow.graphBudget {ι : Type*} (r : RationalRow ι)
    (rate : ι → ℝ) (α β D m : ℝ) : ℝ :=
  KernelBudget.budget r.terms (∅ : Finset ℤ) r.A r.B r.dδ r.dM α β D
    (fun i => (r.price i : ℝ)) rate (fun _ => 0) (fun _ => 0) m

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem RationalRow.graphBudget_le_averaged (r : RationalRow ι) (w : IntervalWitness)
    (hr : r.signCheck = true) (hf : r.fixedIndices = ∅) (N : ℕ)
    (hcertificate : ∀ m ≤ N, ∀ j : ℤ, ∀ q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ),
      0 ≤ r.toReal.residual m j q)
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V))
    (hN : S.card ≤ N) {z : ℝ} (hz : 0 < z)
    (hq : z / (1 + z) ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ))
    (k : ℕ) (hmean : hardCoreMean G S z = k) (α β D : ℝ) (rate : ι → ℝ)
    (hvarK : hardCoreVariance G S z ≤
      (z / (1 + z) * (1 - z / (1 + z)) + α) * hardCoreAvailableMean G S I z + β)
    (hvarM : hardCoreAvailableVariance G S I z ≤ D * hardCoreAvailableMean G S I z)
    (hlap : ∀ i ∈ r.terms, hardCoreLayerLaplace G S I z (r.retention i) ≤
      Real.exp (-rate i * hardCoreAvailableMean G S I z)) :
    r.graphBudget rate α β D (hardCoreAvailableMean G S I z) ≤
      (r.scale : ℝ) * averagedBinomialKernel G S I z r.wL r.wR r.wC k := by
  have hs := of_decide_eq_true hr
  apply averagedBinomialKernel_budget_lower G S I hIS hI hz k hmean r.terms ∅
    r.wL r.wR r.wC r.scale r.A r.B r.C r.dδ r.dM α β D
    (fun i => (r.price i : ℝ)) (fun i => (r.retention i : ℝ)) rate
    (fun _ => 0) (fun _ => 0)
  · exact_mod_cast hs.1.2.2.2.2.1
  · exact_mod_cast hs.1.2.2.2.2.2
  · intro i hi
    exact_mod_cast (hs.2.1 i hi).1
  · simp
  · exact hvarK
  · exact hvarM
  · exact hlap
  · simp
  · intro j _ m hm _
    have hmI : m ≤ I.card := by simpa only [mem_range, Nat.lt_add_one_iff] using hm
    have hmN := hmI.trans ((card_le_card hIS).trans hN)
    have hp := r.toReal.pointwise_lower_of_residual_nonneg m ((k : ℤ) - j)
      (z / (1 + z)) (hcertificate m hmN _ _ hq)
    simp only [toReal, fixed, hf, notMem_empty, if_false, Rat.cast_zero, zero_mul, sub_zero,
      Int.cast_sub, Int.cast_natCast] at hp
    simp only [sum_empty, sub_zero]
    have hδ : (k : ℝ) - j - z / (1 + z) * m = (k : ℝ) - binomialLayerMean j m z := by
      unfold binomialLayerMean
      ring
    simpa only [hδ] using hp

theorem RationalRow.averaged_pos_of_graphBudget (r : RationalRow ι)
    (hr : r.signCheck = true) (G : SimpleGraph V) (S I : Finset V) (z : ℝ) (k : ℕ)
    (α β D : ℝ) (rate : ι → ℝ)
    (hbound : r.graphBudget rate α β D (hardCoreAvailableMean G S I z) ≤
      (r.scale : ℝ) * averagedBinomialKernel G S I z r.wL r.wR r.wC k)
    (hbudget : 0 < r.graphBudget rate α β D (hardCoreAvailableMean G S I z)) :
    0 < averagedBinomialKernel G S I z r.wL r.wR r.wC k := by
  have hs := of_decide_eq_true hr
  have hscale : (0 : ℝ) < r.scale := by exact_mod_cast hs.1.1
  exact (mul_pos_iff_of_pos_left hscale).mp (hbudget.trans_le hbound)

#print axioms RationalRow.graphBudget_le_averaged
#print axioms RationalRow.averaged_pos_of_graphBudget

end ForestUnimodality.FiniteKernelRationalCertificate
