import ForestUnimodality.FiniteKernelRationalCertificate
import Mathlib.Data.Nat.Choose.Sum

/-! Kernel-checked rational mass enclosures propagated in both directions
from one checked pivot. No probabilistic or recurrence premise is supplied. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate
open FiniteKernelRationalCertificate

theorem mass_adjacent (n j : ℕ) (q : ℚ) (hj : j<n) :
    ((j+1:ℕ):ℚ)*(1-q)*mass n ((j+1:ℕ):ℤ) q=
      ((n-j:ℕ):ℚ)*q*mass n (j:ℤ) q := by
  have h0 : (0:ℤ)≤j := by omega
  have h1 : (0:ℤ)≤(j+1:ℕ) := by omega
  have hj0 : (j:ℤ)≤n := by omega
  have hj1 : ((j+1:ℕ):ℤ)≤n := by omega
  simp only [mass,if_pos (And.intro h0 hj0),if_pos (And.intro h1 hj1),Int.toNat_natCast]
  have hc : ((n.choose (j+1):ℕ):ℚ)*((j+1:ℕ):ℚ)=
      (n.choose j:ℚ)*((n-j:ℕ):ℚ) := by exact_mod_cast Nat.choose_succ_right_eq n j
  have hn : n-j=(n-(j+1))+1 := by omega
  rw [hn,pow_succ,pow_succ]
  rw [hn] at hc
  linear_combination hc * ((1-q)*q^j*q*(1-q)^(n-(j+1)))

/-- Only the pivot uses a binomial coefficient, evaluated by the proved
fast factorial-ratio implementation instead of Pascal recursion. -/
def seed (n j : ℕ) (q : ℚ) : ℚ :=
  (Nat.fast_choose n j:ℚ)*q^j*(1-q)^(n-j)

theorem seed_eq_mass (n j : ℕ) (q : ℚ) (hj : j≤n) : seed n j q=mass n (j:ℤ) q := by
  simp [seed,mass,hj,Nat.choose_eq_fast_choose]

structure Table (n : ℕ) where
  pivot : ℕ
  lowerValues : Array ℚ
  upperValues : Array ℚ

def Table.lower {n : ℕ} (t : Table n) (j : ℕ) : ℚ := t.lowerValues.getD j 0
def Table.upper {n : ℕ} (t : Table n) (j : ℕ) : ℚ := t.upperValues.getD j 0

def Table.Valid {n : ℕ} (t : Table n) (q : ℚ) : Prop :=
  0<q ∧ q<1 ∧ t.pivot≤n ∧ t.lowerValues.size=n+1 ∧ t.upperValues.size=n+1 ∧
  t.lower t.pivot≤seed n t.pivot q ∧ seed n t.pivot q≤t.upper t.pivot ∧
  ∀j:Fin n,if j.val<t.pivot then
    ((n-j.val:ℕ):ℚ)*q*t.lower j.val≤((j.val+1:ℕ):ℚ)*(1-q)*t.lower (j.val+1) ∧
    ((j.val+1:ℕ):ℚ)*(1-q)*t.upper (j.val+1)≤((n-j.val:ℕ):ℚ)*q*t.upper j.val
  else
    ((j.val+1:ℕ):ℚ)*(1-q)*t.lower (j.val+1)≤((n-j.val:ℕ):ℚ)*q*t.lower j.val ∧
    ((n-j.val:ℕ):ℚ)*q*t.upper j.val≤((j.val+1:ℕ):ℚ)*(1-q)*t.upper (j.val+1)

instance {n : ℕ} (t : Table n) (q : ℚ) : Decidable (t.Valid q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def Table.check {n : ℕ} (t : Table n) (q : ℚ) : Bool := decide (t.Valid q)
theorem Table.check_valid {n : ℕ} {t : Table n} {q : ℚ} (h : t.check q=true) : t.Valid q :=
  of_decide_eq_true h

theorem Table.step_right {n : ℕ} {t : Table n} {q : ℚ} (h : t.Valid q)
    {j : ℕ} (hj : j<n) (hjp : t.pivot≤j)
    (hlo : t.lower j≤mass n (j:ℤ) q) (hhi : mass n (j:ℤ) q≤t.upper j) :
    t.lower (j+1)≤mass n ((j+1:ℕ):ℤ) q ∧
    mass n ((j+1:ℕ):ℤ) q≤t.upper (j+1) := by
  have hedge:=h.2.2.2.2.2.2.2 ⟨j,hj⟩
  simp only [show ¬j<t.pivot by omega,if_false] at hedge
  have hA : (0:ℚ)<((j+1:ℕ):ℚ)*(1-q) := mul_pos (by positivity) (sub_pos.mpr h.2.1)
  have hB : (0:ℚ)≤((n-j:ℕ):ℚ)*q := mul_nonneg (by positivity) h.1.le
  have hadj:=mass_adjacent n j q hj
  constructor
  · apply (mul_le_mul_iff_right₀ hA).mp
    exact hedge.1.trans (hadj ▸ mul_le_mul_of_nonneg_left hlo hB)
  · apply (mul_le_mul_iff_right₀ hA).mp
    rw [hadj]
    exact (mul_le_mul_of_nonneg_left hhi hB).trans hedge.2

theorem Table.step_left {n : ℕ} {t : Table n} {q : ℚ} (h : t.Valid q)
    {j : ℕ} (hj : j<n) (hjp : j<t.pivot)
    (hlo : t.lower (j+1)≤mass n ((j+1:ℕ):ℤ) q)
    (hhi : mass n ((j+1:ℕ):ℤ) q≤t.upper (j+1)) :
    t.lower j≤mass n (j:ℤ) q ∧ mass n (j:ℤ) q≤t.upper j := by
  have hedge:=h.2.2.2.2.2.2.2 ⟨j,hj⟩
  simp only [hjp,if_true] at hedge
  have hA : (0:ℚ)≤((j+1:ℕ):ℚ)*(1-q) := mul_nonneg (by positivity) (sub_nonneg.mpr h.2.1.le)
  have hB : (0:ℚ)<((n-j:ℕ):ℚ)*q := mul_pos (by exact_mod_cast Nat.sub_pos_of_lt hj) h.1
  have hadj:=mass_adjacent n j q hj
  constructor
  · apply (mul_le_mul_iff_right₀ hB).mp
    rw [←hadj]
    exact hedge.1.trans (mul_le_mul_of_nonneg_left hlo hA)
  · apply (mul_le_mul_iff_right₀ hB).mp
    rw [←hadj]
    exact (mul_le_mul_of_nonneg_left hhi hA).trans hedge.2

theorem Table.valid_sound {n : ℕ} {t : Table n} {q : ℚ} (h : t.Valid q)
    (j : ℕ) (hj : j≤n) : t.lower j≤mass n (j:ℤ) q ∧ mass n (j:ℤ) q≤t.upper j := by
  have hp : t.lower t.pivot≤mass n (t.pivot:ℤ) q ∧ mass n (t.pivot:ℤ) q≤t.upper t.pivot :=
    by simpa only [seed_eq_mass n t.pivot q h.2.2.1] using
      And.intro h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
  by_cases hle : t.pivot≤j
  · induction j,hle using Nat.le_induction with
    | base => exact hp
    | succ j hle ih =>
      have hh:=ih (by omega)
      exact t.step_right h (by omega) hle hh.1 hh.2
  · have hdown : ∀d k:ℕ,k+d=t.pivot→
        t.lower k≤mass n (k:ℤ) q ∧ mass n (k:ℤ) q≤t.upper k := by
      intro d
      induction d with
      | zero =>
        intro k hk
        simp only [Nat.add_zero] at hk
        simpa only [hk] using hp
      | succ d ih =>
        intro k hk
        have hi:=ih (k+1) (by omega)
        exact t.step_left h (by have :=h.2.2.1; omega) (by omega) hi.1 hi.2
    exact hdown (t.pivot-j) j (by omega)

theorem Table.check_sound {n : ℕ} {t : Table n} {q : ℚ} (h : t.check q=true)
    (j : ℕ) (hj : j≤n) : t.lower j≤mass n (j:ℤ) q ∧ mass n (j:ℤ) q≤t.upper j :=
  Table.valid_sound (Table.check_valid h) j hj

theorem Table.real_sound {n : ℕ} {t : Table n} {q : ℚ} (h : t.check q=true)
    (j : ℕ) (hj : j≤n) : (t.lower j:ℝ)≤binomialMass n (j:ℤ) (q:ℝ) ∧
      binomialMass n (j:ℤ) (q:ℝ)≤(t.upper j:ℝ) := by
  have hh:=Table.check_sound h j hj
  rw [←cast_mass]
  exact ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩

#print axioms mass_adjacent
#print axioms Table.check_sound
#print axioms Table.real_sound
end ForestUnimodality.BinomialMassIntervalCertificate
