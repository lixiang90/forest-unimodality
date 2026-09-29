import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A computable coefficient-list polynomial representation. Trailing zeros
are permitted. Equality certificates check every coefficient of a difference;
the semantics below prove equality at every real input. Nesting the coefficient
type gives an executable bivariate representation without noncomputable
Mathlib polynomial multiplication entering the checker. -/

namespace ForestUnimodality.PolynomialList

structure Poly (R : Type*) where
  coeffs : List R
  deriving DecidableEq, Repr

def addList {R : Type*} [Add R] : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addList p q

def mulList {R : Type*} [Zero R] [Add R] [Mul R] : List R → List R → List R
  | [], _ => []
  | a :: p, q => addList (q.map (fun b => a * b)) (0 :: mulList p q)

instance {R : Type*} : Zero (Poly R) := ⟨⟨[]⟩⟩
instance {R : Type*} [One R] : One (Poly R) := ⟨⟨[1]⟩⟩
instance {R : Type*} [Add R] : Add (Poly R) := ⟨fun p q => ⟨addList p.coeffs q.coeffs⟩⟩
instance {R : Type*} [Neg R] : Neg (Poly R) := ⟨fun p => ⟨p.coeffs.map Neg.neg⟩⟩
instance {R : Type*} [Add R] [Neg R] : Sub (Poly R) := ⟨fun p q => p + -q⟩
instance {R : Type*} [Zero R] [Add R] [Mul R] : Mul (Poly R) :=
  ⟨fun p q => ⟨mulList p.coeffs q.coeffs⟩⟩

def pow {R : Type*} [One R] [Zero R] [Add R] [Mul R] (p : Poly R) : ℕ → Poly R
  | 0 => 1
  | n + 1 => pow p n * p

def C {R : Type*} (a : R) : Poly R := ⟨[a]⟩
def X {R : Type*} [Zero R] [One R] : Poly R := ⟨[0, 1]⟩

def sum {R : Type*} [Add R] (ps : List (Poly R)) : Poly R := ps.foldr (· + ·) 0

def comp {R : Type*} [Zero R] [Add R] [Mul R] (p q : Poly R) : Poly R :=
  p.coeffs.foldr (fun a r => C a + q * r) 0

def map {R S : Type*} (f : R → S) (p : Poly R) : Poly S := ⟨p.coeffs.map f⟩

structure Evaluation (R : Type*) [Zero R] [One R] [Add R] [Mul R] [Neg R] where
  value : R → ℝ
  zero : value 0 = 0
  one : value 1 = 1
  add : ∀ a b, value (a + b) = value a + value b
  mul : ∀ a b, value (a * b) = value a * value b
  neg : ∀ a, value (-a) = -value a

def evalList {R : Type*} (f : R → ℝ) (x : ℝ) : List R → ℝ
  | [] => 0
  | a :: p => f a + x * evalList f x p

def eval {R : Type*} (f : R → ℝ) (x : ℝ) (p : Poly R) : ℝ := evalList f x p.coeffs

theorem eval_map {R S : Type*} (f : R → S) (g : S → ℝ) (x : ℝ) (p : Poly R) :
    eval g x (map f p) = eval (fun a => g (f a)) x p := by
  rcases p with ⟨p⟩
  induction p with
  | nil => rfl
  | cons a p ih =>
    change g (f a) + x * eval g x (map f ⟨p⟩) = g (f a) + x * eval (fun b => g (f b)) x ⟨p⟩
    rw [ih]

section Semantics
variable {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
variable (h : Evaluation R) (x : ℝ)

theorem evalList_add (p q : List R) :
    evalList h.value x (addList p q) = evalList h.value x p + evalList h.value x q := by
  induction p generalizing q with
  | nil => simp [addList, evalList]
  | cons a p ih =>
    cases q with
    | nil => simp [addList, evalList]
    | cons b q => simp only [addList, evalList, h.add, ih]; ring

theorem evalList_scale (a : R) (p : List R) :
    evalList h.value x (p.map (fun b => a * b)) = h.value a * evalList h.value x p := by
  induction p with
  | nil => simp [evalList]
  | cons b p ih => simp only [List.map_cons, evalList, h.mul, ih]; ring

theorem evalList_mul (p q : List R) :
    evalList h.value x (mulList p q) = evalList h.value x p * evalList h.value x q := by
  induction p with
  | nil => simp [mulList, evalList]
  | cons a p ih =>
    rw [mulList, evalList_add h x, evalList_scale h x]
    simp only [evalList, h.zero, zero_add, ih]
    ring

theorem evalList_neg (p : List R) :
    evalList h.value x (p.map Neg.neg) = -evalList h.value x p := by
  induction p with
  | nil => simp [evalList]
  | cons a p ih => simp only [List.map_cons, evalList, h.neg, ih]; ring

@[simp] theorem eval_zero : eval h.value x (0 : Poly R) = 0 := rfl
@[simp] theorem eval_one : eval h.value x (1 : Poly R) = 1 := by simp [eval, evalList, h.one]
@[simp] theorem eval_C (a : R) : eval h.value x (C a) = h.value a := by simp [eval, C, evalList]
@[simp] theorem eval_X : eval h.value x (X : Poly R) = x := by simp [eval, X, evalList, h.zero, h.one]
@[simp] theorem eval_add (p q : Poly R) :
    eval h.value x (p + q) = eval h.value x p + eval h.value x q := evalList_add h x _ _
@[simp] theorem eval_mul (p q : Poly R) :
    eval h.value x (p * q) = eval h.value x p * eval h.value x q := evalList_mul h x _ _
@[simp] theorem eval_neg (p : Poly R) : eval h.value x (-p) = -eval h.value x p := evalList_neg h x _
@[simp] theorem eval_sub (p q : Poly R) :
    eval h.value x (p - q) = eval h.value x p - eval h.value x q := by
  change eval h.value x (p + -q) = _
  rw [eval_add, eval_neg]
  rfl
@[simp] theorem eval_pow (p : Poly R) (n : ℕ) : eval h.value x (pow p n) = eval h.value x p ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => rw [pow, eval_mul, ih, pow_succ]

@[simp] theorem eval_sum (ps : List (Poly R)) :
    eval h.value x (sum ps) = (ps.map (eval h.value x)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [sum, List.foldr_cons, eval_add, List.map_cons, List.sum_cons]; exact congrArg _ ih

@[simp] theorem eval_comp (p q : Poly R) :
    eval h.value x (comp p q) = eval h.value (eval h.value x q) p := by
  rcases p with ⟨p⟩
  induction p with
  | nil => rfl
  | cons a p ih =>
    change eval h.value x (C a + q * comp ⟨p⟩ q) = _
    rw [eval_add, eval_C, eval_mul, ih]
    rfl

noncomputable def liftEvaluation : Evaluation (Poly R) where
  value := eval h.value x
  zero := eval_zero h x
  one := eval_one h x
  add := eval_add h x
  mul := eval_mul h x
  neg := eval_neg h x

end Semantics

noncomputable def rationalEvaluation : Evaluation ℚ where
  value := fun a => (a : ℝ)
  zero := Rat.cast_zero
  one := Rat.cast_one
  add := Rat.cast_add
  mul := Rat.cast_mul
  neg := Rat.cast_neg

def zeroCheck {R : Type*} (isZero : R → Bool) (p : Poly R) : Bool := p.coeffs.all isZero
def equalCheck {R : Type*} [Add R] [Neg R] (isZero : R → Bool) (p q : Poly R) : Bool :=
  zeroCheck isZero (p - q)

theorem zeroCheck_sound {R : Type*} (f : R → ℝ) (isZero : R → Bool)
    (hz : ∀ a, isZero a = true → f a = 0) {p : Poly R} (h : zeroCheck isZero p = true) (x : ℝ) :
    eval f x p = 0 := by
  rcases p with ⟨p⟩
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hp : isZero a = true ∧ p.all isZero = true := by simpa [zeroCheck] using h
    change f a + x * eval f x ⟨p⟩ = 0
    rw [hz a hp.1, ih hp.2]
    ring

theorem equalCheck_sound {R : Type*} [Zero R] [One R] [Add R] [Mul R] [Neg R]
    (hR : Evaluation R) (isZero : R → Bool) (hz : ∀ a, isZero a = true → hR.value a = 0)
    {p q : Poly R} (h : equalCheck isZero p q = true) (x : ℝ) :
    eval hR.value x p = eval hR.value x q := by
  have heq := zeroCheck_sound hR.value isZero hz h x
  rw [eval_sub hR] at heq
  exact sub_eq_zero.mp heq

/-- Canonical mathematical polynomial associated with the complete list. -/
noncomputable def toPolynomial (p : Poly ℚ) : Polynomial ℚ :=
  p.coeffs.foldr (fun a q => Polynomial.C a + Polynomial.X * q) 0

theorem eval_toPolynomial (p : Poly ℚ) (x : ℝ) :
    (toPolynomial p).eval₂ (Rat.castHom ℝ) x = eval rationalEvaluation.value x p := by
  rcases p with ⟨p⟩
  induction p with
  | nil => simp [toPolynomial, eval, evalList]
  | cons a p ih =>
    change (Polynomial.C a + Polynomial.X * toPolynomial ⟨p⟩).eval₂ _ _ = _
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Rat.coe_castHom, ih]
    rfl

/-- The executable coefficient test proves the complete mathematical
polynomial identity, and hence equality of every coefficient. -/
theorem equalCheck_toPolynomial_eq {p q : Poly ℚ}
    (h : equalCheck (fun a : ℚ => decide (a = 0)) p q = true) :
    toPolynomial p = toPolynomial q := by
  letI : Infinite ℝ := Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective
  apply Polynomial.map_injective (f := Rat.castHom ℝ) Rat.cast_injective
  apply Polynomial.funext
  intro x
  rw [Polynomial.eval_map, Polynomial.eval_map, eval_toPolynomial, eval_toPolynomial]
  apply equalCheck_sound rationalEvaluation _ _ h x
  intro a ha
  have ha' : a = 0 := of_decide_eq_true ha
  simp [ha', rationalEvaluation]

#print axioms equalCheck_sound
#print axioms eval_toPolynomial
#print axioms equalCheck_toPolynomial_eq

end ForestUnimodality.PolynomialList
