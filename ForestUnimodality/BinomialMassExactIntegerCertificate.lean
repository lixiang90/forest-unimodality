import ForestUnimodality.BinomialMassIntegerCertificate

/-! A wholly integral checker, including the single binomial pivot. It is
proved equivalent in the required direction to the rational mass checker. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

theorem seed_mul_den_pow (n j a b : ℕ) (hj : j≤n) (hab : a≤b) (hb : 0<b) :
    seed n j ((a:ℚ)/b)*(b:ℚ)^n=
      (Nat.fast_choose n j:ℚ)*(a:ℚ)^j*((b-a:ℕ):ℚ)^(n-j) := by
  have hb0 : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  have hcomp : 1-(a:ℚ)/b=((b-a:ℕ):ℚ)/b := by
    rw [Nat.cast_sub hab]
    field_simp
  have hpow : (b:ℚ)^j*(b:ℚ)^(n-j)=(b:ℚ)^n := by rw [←pow_add,Nat.add_sub_of_le hj]
  unfold seed
  rw [hcomp,div_pow,div_pow]
  have hn0 : (b:ℚ)^n≠0 := pow_ne_zero _ hb0
  calc
    (Nat.fast_choose n j:ℚ)*((a:ℚ)^j/(b:ℚ)^j)*
        (((b-a:ℕ):ℚ)^(n-j)/(b:ℚ)^(n-j))*(b:ℚ)^n =
      ((Nat.fast_choose n j:ℚ)*(a:ℚ)^j*((b-a:ℕ):ℚ)^(n-j))/
        ((b:ℚ)^j*(b:ℚ)^(n-j))*(b:ℚ)^n := by ring
    _ = _ := by rw [hpow]; exact div_mul_cancel₀ _ hn0

def IntegerTable.pivotNumerator {n : ℕ} (t : IntegerTable n) (a b : ℕ) : ℤ :=
  (t.denominator*Nat.fast_choose n t.pivot*a^t.pivot*(b-a)^(n-t.pivot):ℕ)

def IntegerTable.ExactValid {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Prop :=
  0<a ∧ a<b ∧ 0<t.denominator ∧ t.pivot≤n ∧
  t.lowerValues.size=n+1 ∧ t.upperValues.size=n+1 ∧
  t.lowerNumerator t.pivot*(b^n:ℕ)≤t.pivotNumerator a b ∧
  t.pivotNumerator a b≤t.upperNumerator t.pivot*(b^n:ℕ) ∧
  ∀j:Fin n,if j.val<t.pivot then
    rightFactor n a j.val*t.lowerNumerator j.val≤leftFactor a b j.val*t.lowerNumerator (j.val+1) ∧
    leftFactor a b j.val*t.upperNumerator (j.val+1)≤rightFactor n a j.val*t.upperNumerator j.val
  else
    leftFactor a b j.val*t.lowerNumerator (j.val+1)≤rightFactor n a j.val*t.lowerNumerator j.val ∧
    rightFactor n a j.val*t.upperNumerator j.val≤leftFactor a b j.val*t.upperNumerator (j.val+1)
instance {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Decidable (t.ExactValid a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def IntegerTable.exactCheck {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Bool := decide (t.ExactValid a b)

theorem IntegerTable.exactValid_valid {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.ExactValid a b) : t.Valid a b := by
  have hb : 0<b := h.1.trans h.2.1
  have hp : (0:ℚ)<(b:ℚ)^n := pow_pos (by exact_mod_cast hb) n
  have hs:=seed_mul_den_pow n t.pivot a b h.2.2.2.1 h.2.1.le hb
  have he : (t.pivotNumerator a b:ℚ)=(b:ℚ)^n*((t.denominator:ℚ)*seed n t.pivot ((a:ℚ)/b)) := by
    simp only [pivotNumerator]
    push_cast
    linear_combination -(t.denominator:ℚ)*hs
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,?_,?_,h.2.2.2.2.2.2.2.2⟩
  · apply (mul_le_mul_iff_right₀ hp).mp
    rw [←he,mul_comm]
    exact_mod_cast h.2.2.2.2.2.2.1
  · apply (mul_le_mul_iff_right₀ hp).mp
    rw [←he,mul_comm ((b:ℚ)^n)]
    exact_mod_cast h.2.2.2.2.2.2.2.1

theorem IntegerTable.exactCheck_sound {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.exactCheck a b=true) (j : ℕ) (hj : j≤n) :
    t.lower j≤FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b) ∧
    FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b)≤t.upper j := by
  have hv : t.ExactValid a b := of_decide_eq_true h
  simpa only [toTable_lower,toTable_upper] using Table.valid_sound
    (IntegerTable.toTable_valid (IntegerTable.exactValid_valid hv)) j hj

#print axioms seed_mul_den_pow
#print axioms IntegerTable.exactCheck_sound
end ForestUnimodality.BinomialMassIntervalCertificate
