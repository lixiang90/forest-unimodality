import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A checked interval chain covers every real point, not just endpoints.
The lower boundary is open so an independently proved origin interval can
be joined to the finite chain without a degenerate empty-list exception. -/
namespace ForestUnimodality.SourceIntervalCoverage

def check {α : Type*} (left right : α → ℚ) (lower upper : ℚ) : List α → Bool
  | [] => decide (upper ≤ lower)
  | cell :: rest => decide (left cell ≤ lower ∧ lower ≤ right cell) &&
      check left right (right cell) upper rest

theorem check_sound {α : Type*} (left right : α → ℚ) {lower upper : ℚ} {cells : List α}
    (h : check left right lower upper cells=true) {p : ℝ}
    (hp : (lower : ℝ) < p) (hpu : p ≤ (upper : ℝ)) :
    ∃ cell ∈ cells, (left cell : ℝ) ≤ p ∧ p ≤ (right cell : ℝ) := by
  induction cells generalizing lower with
  | nil =>
    have hq : upper ≤ lower := of_decide_eq_true h
    have hr : (upper : ℝ) ≤ lower := by exact_mod_cast hq
    exact (not_lt_of_ge (hpu.trans hr) hp).elim
  | cons cell rest ih =>
    have hh : decide (left cell ≤ lower ∧ lower ≤ right cell)=true ∧
        check left right (right cell) upper rest=true := by
      simpa only [check, Bool.and_eq_true_iff] using h
    have hq : left cell ≤ lower ∧ lower ≤ right cell := of_decide_eq_true hh.1
    by_cases hpr : p ≤ (right cell : ℝ)
    · refine ⟨cell, by simp, ?_, hpr⟩
      have hl : (left cell : ℝ) ≤ lower := by exact_mod_cast hq.1
      exact hl.trans hp.le
    · obtain ⟨found,hfound,hfl,hfr⟩ := ih hh.2 (lt_of_not_ge hpr)
      exact ⟨found, List.mem_cons_of_mem cell hfound, hfl, hfr⟩

theorem property_of_check {α : Type*} (left right : α → ℚ) {lower upper : ℚ} {cells : List α}
    (h : check left right lower upper cells=true) (P : ℝ → Prop)
    (hcell : ∀ cell ∈ cells, ∀ p : ℝ, (left cell : ℝ) ≤ p → p ≤ (right cell : ℝ) → P p)
    {p : ℝ} (hp : (lower : ℝ) < p) (hpu : p ≤ (upper : ℝ)) : P p := by
  obtain ⟨cell,hmem,hl,hr⟩ := check_sound left right h hp hpu
  exact hcell cell hmem p hl hr

theorem property_with_origin {α : Type*} (left right : α → ℚ) {lower upper : ℚ} {cells : List α}
    (h : check left right lower upper cells=true) (P : ℝ → Prop)
    (horigin : ∀ p : ℝ, 0 < p → p ≤ (lower : ℝ) → P p)
    (hcell : ∀ cell ∈ cells, ∀ p : ℝ, 0 < p →
      (left cell : ℝ) ≤ p → p ≤ (right cell : ℝ) → P p)
    {p : ℝ} (hp : 0 < p) (hpu : p ≤ (upper : ℝ)) : P p := by
  by_cases hpl : p ≤ (lower : ℝ)
  · exact horigin p hp hpl
  · obtain ⟨cell,hmem,hl,hr⟩ := check_sound left right h (lt_of_not_ge hpl) hpu
    exact hcell cell hmem p hp hl hr

#print axioms check_sound
#print axioms property_with_origin
end ForestUnimodality.SourceIntervalCoverage
