import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Exact closed interval and rectangle covers. Soundness is for arbitrary
real points, including shared endpoints; no grid sampling is used. -/
namespace ForestUnimodality.FiniteRectangleCover

def chainCheck {ι : Type*} (bounds : ι → ℚ × ℚ) : List ι → ℚ → ℚ → Bool
  | [], _, _ => false
  | i :: rest, a, b =>
      decide ((bounds i).1 ≤ a) &&
        (decide (b ≤ (bounds i).2) || chainCheck bounds rest (max a (bounds i).2) b)

theorem chainCheck_sound {ι : Type*} (bounds : ι → ℚ × ℚ) (indices : List ι)
    {a b : ℚ} (hc : chainCheck bounds indices a b = true)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    ∃ i ∈ indices, x ∈ Set.Icc ((bounds i).1 : ℝ) ((bounds i).2 : ℝ) := by
  induction indices generalizing a with
  | nil => simp [chainCheck] at hc
  | cons i rest ih =>
      have hp : (bounds i).1 ≤ a ∧
          (b ≤ (bounds i).2 ∨ chainCheck bounds rest (max a (bounds i).2) b = true) := by
        simpa only [chainCheck, Bool.and_eq_true_iff, Bool.or_eq_true_iff,
          decide_eq_true_eq] using hc
      by_cases hhi : x ≤ ((bounds i).2 : ℝ)
      · exact ⟨i, by simp, (show ((bounds i).1 : ℝ) ≤ (a : ℝ) by
          exact_mod_cast hp.1).trans hx.1, hhi⟩
      · have htail : chainCheck bounds rest (max a (bounds i).2) b = true := by
          rcases hp.2 with h | h
          · have hr : (b : ℝ) ≤ ((bounds i).2 : ℝ) := by exact_mod_cast h
            exact False.elim (hhi (hx.2.trans hr))
          · exact h
        have hmax : ((max a (bounds i).2 : ℚ) : ℝ) ≤ x := by
          rw [Rat.cast_max]
          exact max_le hx.1 (le_of_not_ge hhi)
        obtain ⟨j, hj, hpoint⟩ := ih htail ⟨hmax, hx.2⟩
        exact ⟨j, List.mem_cons_of_mem i hj, hpoint⟩

structure Rectangle where
  qlo : ℚ
  qhi : ℚ
  mlo : ℚ
  mhi : ℚ

def Rectangle.Contains (r : Rectangle) (q m : ℝ) : Prop :=
  q ∈ Set.Icc (r.qlo : ℝ) (r.qhi : ℝ) ∧
    m ∈ Set.Icc (r.mlo : ℝ) (r.mhi : ℝ)

structure Strip (ι : Type*) where
  qlo : ℚ
  qhi : ℚ
  mlo : ℚ
  mhi : ℚ
  cells : List ι

def Strip.check {ι : Type*} (s : Strip ι) (rectangles : ι → Rectangle) : Bool :=
  s.cells.all (fun i => decide ((rectangles i).qlo ≤ s.qlo ∧ s.qhi ≤ (rectangles i).qhi)) &&
    chainCheck (fun i => ((rectangles i).mlo, (rectangles i).mhi)) s.cells s.mlo s.mhi

theorem Strip.check_sound {ι : Type*} (s : Strip ι) (rectangles : ι → Rectangle)
    (hc : s.check rectangles = true) {q m : ℝ}
    (hq : q ∈ Set.Icc (s.qlo : ℝ) (s.qhi : ℝ))
    (hm : m ∈ Set.Icc (s.mlo : ℝ) (s.mhi : ℝ)) :
    ∃ i ∈ s.cells, (rectangles i).Contains q m := by
  have hp : (∀ i ∈ s.cells, (rectangles i).qlo ≤ s.qlo ∧ s.qhi ≤ (rectangles i).qhi) ∧
      chainCheck (fun i => ((rectangles i).mlo, (rectangles i).mhi)) s.cells s.mlo s.mhi = true := by
    simpa only [check, Bool.and_eq_true_iff, List.all_eq_true, decide_eq_true_eq] using hc
  obtain ⟨i, hi, hmi⟩ := chainCheck_sound _ s.cells hp.2 hm
  have hqi := hp.1 i hi
  have hl : ((rectangles i).qlo : ℝ) ≤ (s.qlo : ℝ) := by exact_mod_cast hqi.1
  have hu : (s.qhi : ℝ) ≤ ((rectangles i).qhi : ℝ) := by exact_mod_cast hqi.2
  exact ⟨i, hi, ⟨hl.trans hq.1, hq.2.trans hu⟩, hmi⟩

/-- A checked horizontal cover followed by a checked vertical cover locates
the actual point in a certified rectangle. The lower and upper expectation
bounds may depend on the horizontal strip selected by the first cover. -/
theorem exists_rectangle {ι σ : Type*} (rectangles : ι → Rectangle)
    (strips : σ → Strip ι) (indices : List σ) (a b : ℚ)
    (hqcover : chainCheck (fun s => ((strips s).qlo, (strips s).qhi)) indices a b = true)
    (hstrips : ∀ s ∈ indices, (strips s).check rectangles = true)
    {q m : ℝ} (hq : q ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hm : ∀ s ∈ indices, q ∈ Set.Icc ((strips s).qlo : ℝ) ((strips s).qhi : ℝ) →
      m ∈ Set.Icc ((strips s).mlo : ℝ) ((strips s).mhi : ℝ)) :
    ∃ i, (rectangles i).Contains q m := by
  obtain ⟨s, hs, hqs⟩ := chainCheck_sound _ indices hqcover hq
  obtain ⟨i, _, hi⟩ := (strips s).check_sound rectangles (hstrips s hs) hqs (hm s hs hqs)
  exact ⟨i, hi⟩

#print axioms chainCheck_sound
#print axioms Strip.check_sound
#print axioms exists_rectangle

end ForestUnimodality.FiniteRectangleCover
