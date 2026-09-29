import ForestUnimodality.ShortLegData

/-! All positive path lengths, proved by the exact transfer recurrence.
The closed forms are established symbolically; no finite sampling bound is
used to infer the general statement. -/

namespace ForestUnimodality.PathAdjustedMean

noncomputable def pathZ (n : ℕ) : ℝ := (2 ^ (n + 2) - (-1) ^ n) / 3

noncomputable def pathM (n : ℕ) : ℝ :=
  ((3 * (n : ℝ) + 2) * pathZ n - ((n : ℝ) + 2) * (-1) ^ n) / 9

theorem pathZ_recurrence (n : ℕ) : pathZ (n + 2) = pathZ (n + 1) + 2 * pathZ n := by
  simp only [pathZ, pow_succ]
  ring

theorem pathM_recurrence (n : ℕ) :
    pathM (n + 2) = pathM (n + 1) + 2 * (pathM n + pathZ n) := by
  simp only [pathM, pathZ, Nat.cast_add, Nat.cast_ofNat, pow_succ]
  ring

theorem transfer_closed (n : ℕ) :
    pathMomentTransfer 2 n (3, 2, 1, 0) =
      (pathZ (n + 1), pathM (n + 1), pathZ n, pathM n) := by
  induction n with
  | zero => norm_num [pathMomentTransfer, pathZ, pathM]
  | succ n ih =>
    rw [pathMomentTransfer, ih]
    exact Prod.ext (pathZ_recurrence n).symm
      (Prod.ext (pathM_recurrence n).symm rfl)

theorem statistics_closed (n : ℕ) (hn : 0 < n) :
    pathBranchStatistics n = (pathZ n, pathM n, pathZ (n - 1), pathM (n - 1)) := by
  unfold pathBranchStatistics
  rw [transfer_closed, Nat.sub_add_cancel hn]

theorem pathZ_positive (n : ℕ) (hn : 0 < n) : 0 < pathZ n := by
  have h := congrArg Prod.fst ((ShortLegData.pathData_cast n).trans (statistics_closed n hn))
  have hp : (0 : ℝ) < (ShortLegData.pathData n).1 := by
    exact_mod_cast (ShortLegData.pathData_positive n).1
  change ((ShortLegData.pathData n).1 : ℝ) = pathZ n at h
  rw [← h]
  exact hp

/-- The numerator of the ordinary path excess 3 mu - n. -/
theorem excess_numerator (n : ℕ) :
    3 * pathM n - (n : ℝ) * pathZ n =
      (2 / 3 : ℝ) * pathZ n - ((n : ℝ) + 2) * (-1) ^ n / 3 := by
  unfold pathM
  ring

theorem power_linear_bound (n : ℕ) (hn : 2 ≤ n) :
    15 * (n : ℝ) + 34 ≤ 4 * 2 ^ (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
    push_cast
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

theorem even_excess_lower (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    (2 / 5 : ℝ) * pathZ n ≤ 3 * pathM n - (n : ℝ) * pathZ n := by
  rw [excess_numerator, heven.neg_one_pow]
  have hp := power_linear_bound n hn
  unfold pathZ
  rw [heven.neg_one_pow]
  nlinarith

theorem odd_excess_lower (n : ℕ) (hodd : Odd n) :
    (2 / 3 : ℝ) * pathZ n < 3 * pathM n - (n : ℝ) * pathZ n := by
  rw [excess_numerator, hodd.neg_one_pow]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem adjusted_path_positive (n : ℕ) (hn : 0 < n) :
    0 < 3 * pathM n / pathZ n - (((n + 1) / 2 : ℕ) : ℝ) - 29 * (n : ℝ) / 60 := by
  have hZ := pathZ_positive n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnum : 0 < 3 * pathM n -
      ((((n + 1) / 2 : ℕ) : ℝ) + 29 * (n : ℝ) / 60) * pathZ n := by
    rcases Nat.even_or_odd n with he | ho
    · have hn2 : 2 ≤ n := by obtain ⟨m, hm⟩ := he; omega
      have ha : 2 * (((n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) := by
        have ha' : 2 * ((n + 1) / 2) = n := by obtain ⟨m, hm⟩ := he; omega
        exact_mod_cast ha'
      have hexc := even_excess_lower n hn2 he
      have hzterm := mul_nonneg hn'.le hZ.le
      nlinarith
    · have ha : 2 * (((n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) + 1 := by
        have ha' : 2 * ((n + 1) / 2) = n + 1 := by obtain ⟨m, hm⟩ := ho; omega
        exact_mod_cast ha'
      have hexc := odd_excess_lower n ho
      have hzterm := mul_nonneg hn'.le hZ.le
      nlinarith
  have hd := (div_pos hnum hZ)
  have heq : 3 * pathM n / pathZ n - (((n + 1) / 2 : ℕ) : ℝ) - 29 * (n : ℝ) / 60 =
      (3 * pathM n - ((((n + 1) / 2 : ℕ) : ℝ) + 29 * (n : ℝ) / 60) * pathZ n) / pathZ n := by
    field_simp
    ring
  rw [heq]
  exact hd

theorem pathData_excess_pos (n : ℕ) (hn : 0 < n) : 0 < ShortLegData.excess n := by
  have ht := (ShortLegData.pathData_cast n).trans (statistics_closed n hn)
  have hZ := congrArg Prod.fst ht
  have hM := congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) ht
  change ((ShortLegData.pathData n).1 : ℝ) = pathZ n at hZ
  change ((ShortLegData.pathData n).2.1 : ℝ) = pathM n at hM
  have hp : (0 : ℝ) < (ShortLegData.excess n : ℝ) := by
    unfold ShortLegData.excess
    push_cast
    rw [hZ, hM]
    exact adjusted_path_positive n hn
  exact_mod_cast hp

#print axioms transfer_closed
#print axioms adjusted_path_positive
#print axioms pathData_excess_pos

end ForestUnimodality.PathAdjustedMean

namespace ForestUnimodality

variable {V : Type*} [DecidableEq V]

/-- Every nonempty actual path, represented by adjoining endpoints to a
singleton, has strictly positive adjusted mean at activity two. The number
of extension steps is arbitrary, including zero for the singleton path. -/
theorem PendantPathExtension.adjustedMean_pos_path
    {G : SimpleGraph V} {S : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) :
    0 < adjustedMeanPotential G S (independenceNumberOn G S) := by
  have ht := h.moment_transfer 2
  rw [hardCore_singleton_statistics] at ht
  norm_num only at ht
  rw [PathAdjustedMean.transfer_closed] at ht
  have hZ := congrArg Prod.fst ht
  have hM := congrArg (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1) ht
  have ha := h.card_transfer
  rw [independenceNumberOn_singleton] at ha
  have he : independenceNumberOn G (∅ : Finset V) = 0 := by
    simp [independenceNumberOn, independentSubsets_empty_eq_singleton]
  simp only [Finset.erase_singleton, he, pathCardTransfer_from_singleton] at ha
  have hα := congrArg Prod.fst ha
  have hc : S.card = n + 1 := by
    have hc := h.card_eq
    simp only [Finset.card_singleton] at hc
    omega
  change partitionFunction G S (2 : ℝ) = PathAdjustedMean.pathZ (n + 1) at hZ
  change hardCoreMomentNumerator G S 1 (2 : ℝ) = PathAdjustedMean.pathM (n + 1) at hM
  change independenceNumberOn G S = (n + 2) / 2 at hα
  unfold adjustedMeanPotential hardCoreMean
  rw [hZ, hM, hα, hc]
  convert PathAdjustedMean.adjusted_path_positive (n + 1) (by omega) using 1
  ring

theorem PendantPathExtension.adjustedMean_pos_maximum
    {G : SimpleGraph V} {S I : Finset V} {v u : V} {n : ℕ}
    (h : PendantPathExtension G {v} v n S u) (hI : IsMaximumIndependentOn G S I) :
    0 < adjustedMeanPotential G S I.card := by
  rw [hI.card_eq_independenceNumberOn]
  exact h.adjustedMean_pos_path

#print axioms PendantPathExtension.adjustedMean_pos_path
#print axioms PendantPathExtension.adjustedMean_pos_maximum

end ForestUnimodality
