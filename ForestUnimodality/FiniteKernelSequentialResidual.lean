import ForestUnimodality.FiniteKernelIntegerCertificate

/-! Linear traversals for integer residual certificates. The three padded
mass streams retain the two support-boundary states on each side. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

open FiniteKernelRationalCertificate

theorem getD_replicate_zero (count i : ℕ) : (List.replicate count (0 : ℤ)).getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_append_zeros (xs : List ℤ) (count i : ℕ) :
    (xs ++ List.replicate count 0).getD i 0 = xs.getD i 0 := by
  induction xs generalizing i with
  | nil =>
    change (List.replicate count (0 : ℤ)).getD i 0 = 0
    exact getD_replicate_zero count i
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa only [List.cons_append, List.getD_cons_succ] using ih i

theorem getD_prefix_zeros (xs : List ℤ) (count i : ℕ) :
    (List.replicate count 0 ++ xs).getD i 0 = if count ≤ i then xs.getD (i - count) 0 else 0 := by
  induction count generalizing i with
  | zero => simp
  | succ count ih =>
    cases i with
    | zero => simp
    | succ i => simpa only [List.replicate_succ, List.cons_append, List.getD_cons_succ,
        Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] using ih i

def paddedStream (values : Array ℤ) (before after : ℕ) : List ℤ :=
  List.replicate before 0 ++ (values.toList ++ List.replicate after 0)

theorem paddedStream_getD (values : Array ℤ) (before after i : ℕ) :
    (paddedStream values before after).getD i 0 =
      if before ≤ i then values.getD (i - before) 0 else 0 := by
  rw [paddedStream, getD_prefix_zeros, getD_append_zeros]
  split_ifs
  · simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  · rfl

def _root_.ForestUnimodality.FiniteKernelRationalCertificate.IntegerResidualPolynomial.streamCheck
    (p : IntegerResidualPolynomial) (n : ℕ)
    (lower upper : Array ℤ) : Bool :=
  ((List.range (n + 5)).zip ((paddedStream lower 2 2).zip
    ((paddedStream upper 3 1).zip (paddedStream upper 1 3)))).all fun entry =>
      let j : ℤ := (entry.1 : ℤ) - 2
      decide (0 ≤ p.center * entry.2.1 - p.previous * entry.2.2.1 - p.next * entry.2.2.2 +
        p.square * j ^ 2 + p.linear * j + p.constant)

theorem paddedStream_integer_index (values : Array ℤ) (n before after i : ℕ)
    (hs : values.size = n + 1) :
    (paddedStream values before after).getD i 0 =
      if 0 ≤ (i : ℤ) - before ∧ (i : ℤ) - before ≤ n then
        values.getD (((i : ℤ) - before).toNat) 0 else 0 := by
  rw [paddedStream_getD]
  by_cases hb : before ≤ i
  · rw [if_pos hb]
    have he : ((i : ℤ) - before).toNat = i - before := by omega
    rw [he]
    by_cases hi : (i : ℤ) - before ≤ n
    · rw [if_pos ⟨by omega, hi⟩]
    · rw [if_neg (by omega)]
      have hout : ¬ i - before < values.size := by omega
      simp [Array.getD, hout]
  · rw [if_neg hb, if_neg (by omega)]

theorem _root_.ForestUnimodality.FiniteKernelRationalCertificate.IntegerResidualPolynomial.streamCheck_sound
    (p : IntegerResidualPolynomial) {n : ℕ}
    (t : IntegerTable n) (hlo : t.lowerValues.size = n + 1) (hhi : t.upperValues.size = n + 1)
    (hc : p.streamCheck n t.lowerValues t.upperValues = true) :
    p.spanCheck n t.lowerNumeratorInt t.upperNumeratorInt = true := by
  apply List.all_eq_true.mpr
  intro i hi
  apply decide_eq_true
  have hi' : i < n + 5 := List.mem_range.mp hi
  have lenL : (paddedStream t.lowerValues 2 2).length = n + 5 := by
    simp [paddedStream, hlo]
  have lenP : (paddedStream t.upperValues 3 1).length = n + 5 := by
    simp [paddedStream, hhi]
  have lenN : (paddedStream t.upperValues 1 3).length = n + 5 := by
    simp [paddedStream, hhi]
  let entries := (List.range (n + 5)).zip ((paddedStream t.lowerValues 2 2).zip
    ((paddedStream t.upperValues 3 1).zip (paddedStream t.upperValues 1 3)))
  have hei : i < entries.length := by simp [entries, lenL, lenP, lenN, hi']
  have hmem : entries[i] ∈ entries := List.getElem_mem hei
  have h := List.all_eq_true.mp hc entries[i] hmem
  have h' := of_decide_eq_true h
  have hgetL : (paddedStream t.lowerValues 2 2)[i]'(by omega) =
      t.lowerNumeratorInt ((i : ℤ) - 2) := by
    have he := paddedStream_integer_index t.lowerValues n 2 2 i hlo
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (paddedStream t.lowerValues 2 2).length by omega),
      Option.getD_some] at he
    norm_num only [Nat.cast_ofNat] at he
    simpa only [IntegerTable.lowerNumeratorInt, IntegerTable.lowerNumerator] using he
  have hgetP : (paddedStream t.upperValues 3 1)[i]'(by omega) =
      t.upperNumeratorInt (((i : ℤ) - 2) - 1) := by
    have he := paddedStream_integer_index t.upperValues n 3 1 i hhi
    have hj : (i : ℤ) - 3 = ((i : ℤ) - 2) - 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (paddedStream t.upperValues 3 1).length by omega),
      Option.getD_some] at he
    norm_num only [Nat.cast_ofNat] at he
    simpa only [hj, IntegerTable.upperNumeratorInt, IntegerTable.upperNumerator] using he
  have hgetN : (paddedStream t.upperValues 1 3)[i]'(by omega) =
      t.upperNumeratorInt (((i : ℤ) - 2) + 1) := by
    have he := paddedStream_integer_index t.upperValues n 1 3 i hhi
    have hj : (i : ℤ) - 1 = ((i : ℤ) - 2) + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < (paddedStream t.upperValues 1 3).length by omega),
      Option.getD_some] at he
    norm_num only [Nat.cast_ofNat] at he
    simpa only [hj, IntegerTable.upperNumeratorInt, IntegerTable.upperNumerator] using he
  simpa only [entries, List.getElem_zip, List.getElem_range,
    hgetL, hgetP, hgetN, IntegerResidualPolynomial.eval] using h'

#print axioms paddedStream_getD
#print axioms IntegerResidualPolynomial.streamCheck_sound

end ForestUnimodality.BinomialMassIntervalCertificate
