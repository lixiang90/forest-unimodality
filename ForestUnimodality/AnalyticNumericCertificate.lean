import ForestUnimodality.ExpEnclosure
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A rational interval certificate interpreter for analytic endpoint budgets.
The expression denotes a real number independently of all witness endpoints. -/
namespace ForestUnimodality.AnalyticNumericCertificate

inductive Expr where
  | rat (q : ℚ)
  | pi
  | add (a b : Expr)
  | sub (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | inv (a : Expr)
  | sqrt (a : Expr) (lo hi : ℚ)
  | exp (q lo hi : ℚ) (certificate : ExpEnclosure.PowerCertificate)
  deriving Repr

def piLower : ℚ := 314159265358979323846 / 100000000000000000000
def piUpper : ℚ := 314159265358979323847 / 100000000000000000000

noncomputable def Expr.eval : Expr → ℝ
  | .rat q => q
  | .pi => Real.pi
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .neg a => -a.eval
  | .mul a b => a.eval * b.eval
  | .inv a => a.eval⁻¹
  | .sqrt a _ _ => Real.sqrt a.eval
  | .exp q _ _ _ => Real.exp q

mutual
def Expr.lower : Expr → ℚ
  | .rat q => q
  | .pi => piLower
  | .add a b => a.lower + b.lower
  | .sub a b => a.lower - b.upper
  | .neg a => -a.upper
  | .mul a b => min (min (a.lower * b.lower) (a.lower * b.upper))
      (min (a.upper * b.lower) (a.upper * b.upper))
  | .inv a => a.upper⁻¹
  | .sqrt _ lo _ => lo
  | .exp _ lo _ _ => lo

def Expr.upper : Expr → ℚ
  | .rat q => q
  | .pi => piUpper
  | .add a b => a.upper + b.upper
  | .sub a b => a.upper - b.lower
  | .neg a => -a.lower
  | .mul a b => max (max (a.lower * b.lower) (a.lower * b.upper))
      (max (a.upper * b.lower) (a.upper * b.upper))
  | .inv a => a.lower⁻¹
  | .sqrt _ _ hi => hi
  | .exp _ _ hi _ => hi
end

def Expr.check : Expr → Bool
  | .rat _ => true
  | .pi => true
  | .add a b => a.check && b.check
  | .sub a b => a.check && b.check
  | .neg a => a.check
  | .mul a b => a.check && b.check
  | .inv a => a.check && decide (0 < a.lower)
  | .sqrt a lo hi => a.check && decide
      (0 ≤ lo ∧ 0 ≤ hi ∧ lo ^ 2 ≤ a.lower ∧ a.upper ≤ hi ^ 2)
  | .exp q lo hi c => c.check q lo hi

theorem mul_interval {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y ∧
      x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have lac : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c :=
    (min_le_left _ _).trans (min_le_left _ _)
  have lad : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d :=
    (min_le_left _ _).trans (min_le_right _ _)
  have lbc : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c :=
    (min_le_right _ _).trans (min_le_left _ _)
  have lbd : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d :=
    (min_le_right _ _).trans (min_le_right _ _)
  have uac : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have uad : a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_left _ _)
  have ubc : b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have ubd : b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · by_cases hx0 : 0 ≤ x
    · have he := mul_le_mul_of_nonneg_left hy.1 hx0
      by_cases hc0 : 0 ≤ c
      · exact lac.trans ((mul_le_mul_of_nonneg_right hx.1 hc0).trans he)
      · exact lbc.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hc0)).trans he)
    · have he := mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hx0)
      by_cases hd0 : 0 ≤ d
      · exact lad.trans ((mul_le_mul_of_nonneg_right hx.1 hd0).trans he)
      · exact lbd.trans ((mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hd0)).trans he)
  · by_cases hx0 : 0 ≤ x
    · have he := mul_le_mul_of_nonneg_left hy.2 hx0
      by_cases hd0 : 0 ≤ d
      · exact (he.trans (mul_le_mul_of_nonneg_right hx.2 hd0)).trans ubd
      · exact (he.trans (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hd0))).trans uad
    · have he := mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hx0)
      by_cases hc0 : 0 ≤ c
      · exact (he.trans (mul_le_mul_of_nonneg_right hx.2 hc0)).trans ubc
      · exact (he.trans (mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hc0))).trans uac

theorem cast_min (a b : ℚ) : ((min a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (by exact_mod_cast h')]

theorem cast_max (a b : ℚ) : ((max a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · have h' : b ≤ a := le_of_not_ge h
    rw [max_eq_left h', max_eq_left (by exact_mod_cast h')]

theorem Expr.check_sound (e : Expr) (hcheck : e.check = true) :
    (e.lower : ℝ) ≤ e.eval ∧ e.eval ≤ (e.upper : ℝ) := by
  induction e with
  | rat q => exact ⟨le_rfl, le_rfl⟩
  | pi =>
    constructor
    · convert! Real.pi_gt_d20.le using 1; norm_num [Expr.lower, Expr.eval, piLower]
    · convert! Real.pi_lt_d20.le using 1; norm_num [Expr.upper, Expr.eval, piUpper]
  | add a b iha ihb =>
    have hc : a.check = true ∧ b.check = true := by simpa only [Expr.check, Bool.and_eq_true_iff] using hcheck
    have ha := iha hc.1
    have hb := ihb hc.2
    simpa only [Expr.lower, Expr.upper, Expr.eval, Rat.cast_add] using
      And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)
  | sub a b iha ihb =>
    have hc : a.check = true ∧ b.check = true := by simpa only [Expr.check, Bool.and_eq_true_iff] using hcheck
    have ha := iha hc.1
    have hb := ihb hc.2
    simpa only [Expr.lower, Expr.upper, Expr.eval, Rat.cast_sub] using
      And.intro (sub_le_sub ha.1 hb.2) (sub_le_sub ha.2 hb.1)
  | neg a iha =>
    have ha := iha hcheck
    simpa only [Expr.lower, Expr.upper, Expr.eval, Rat.cast_neg] using
      And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)
  | mul a b iha ihb =>
    have hc : a.check = true ∧ b.check = true := by simpa only [Expr.check, Bool.and_eq_true_iff] using hcheck
    have he := mul_interval (iha hc.1) (ihb hc.2)
    simpa only [Expr.lower, Expr.upper, Expr.eval, cast_min, cast_max, Rat.cast_mul] using he
  | inv a iha =>
    have hc : a.check = true ∧ 0 < a.lower := by simpa only [Expr.check, Bool.and_eq_true_iff, decide_eq_true_eq] using hcheck
    have ha := iha hc.1
    have hl : (0 : ℝ) < a.lower := by exact_mod_cast hc.2
    have he : 0 < a.eval := hl.trans_le ha.1
    simp only [Expr.lower, Expr.upper, Expr.eval, Rat.cast_inv]
    exact ⟨inv_anti₀ he ha.2, inv_anti₀ hl ha.1⟩
  | sqrt a lo hi iha =>
    have hc : a.check = true ∧ (0 ≤ lo ∧ 0 ≤ hi ∧ lo ^ 2 ≤ a.lower ∧ a.upper ≤ hi ^ 2) := by
      simpa only [Expr.check, Bool.and_eq_true_iff, decide_eq_true_eq] using hcheck
    have ha := iha hc.1
    have hlo : (0 : ℝ) ≤ lo := by exact_mod_cast hc.2.1
    have hhi : (0 : ℝ) ≤ hi := by exact_mod_cast hc.2.2.1
    have hls : (lo : ℝ) ^ 2 ≤ a.lower := by exact_mod_cast hc.2.2.2.1
    have hus : (a.upper : ℝ) ≤ (hi : ℝ) ^ 2 := by exact_mod_cast hc.2.2.2.2
    have he : 0 ≤ a.eval := by nlinarith [sq_nonneg (lo : ℝ)]
    have hs := Real.sq_sqrt he
    have hp := Real.sqrt_nonneg a.eval
    simp only [Expr.lower, Expr.upper, Expr.eval]
    constructor <;> nlinarith
  | exp q lo hi c => exact c.check_sound hcheck

def Expr.positiveCheck (e : Expr) : Bool := e.check && decide (0 < e.lower)

theorem Expr.positiveCheck_sound (e : Expr) (hcheck : e.positiveCheck = true) :
    0 < e.eval := by
  have hc : e.check = true ∧ 0 < e.lower := by
    simpa only [Expr.positiveCheck, Bool.and_eq_true_iff, decide_eq_true_eq] using hcheck
  have hl : (0 : ℝ) < e.lower := by exact_mod_cast hc.2
  exact hl.trans_le (e.check_sound hc.1).1

#print axioms Expr.check_sound
#print axioms Expr.positiveCheck_sound
end ForestUnimodality.AnalyticNumericCertificate
