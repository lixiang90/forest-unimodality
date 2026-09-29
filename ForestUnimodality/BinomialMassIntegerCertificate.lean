import ForestUnimodality.BinomialMassIntervalCertificate

/-! Shared-denominator integer witnesses. Every adjacent test uses only
integer multiplication; just the pivot uses the exact rational mass. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

structure IntegerTable (n : ℕ) where
  pivot : ℕ
  denominator : ℕ
  lowerValues : Array ℤ
  upperValues : Array ℤ

def IntegerTable.lowerNumerator {n : ℕ} (t : IntegerTable n) (j : ℕ) : ℤ := t.lowerValues.getD j 0
def IntegerTable.upperNumerator {n : ℕ} (t : IntegerTable n) (j : ℕ) : ℤ := t.upperValues.getD j 0
def IntegerTable.lower {n : ℕ} (t : IntegerTable n) (j : ℕ) : ℚ := t.lowerNumerator j/t.denominator
def IntegerTable.upper {n : ℕ} (t : IntegerTable n) (j : ℕ) : ℚ := t.upperNumerator j/t.denominator

def IntegerTable.toTable {n : ℕ} (t : IntegerTable n) : Table n where
  pivot := t.pivot
  lowerValues := t.lowerValues.map (fun v:ℤ=>(v:ℚ)/t.denominator)
  upperValues := t.upperValues.map (fun v:ℤ=>(v:ℚ)/t.denominator)

theorem IntegerTable.toTable_lower {n : ℕ} (t : IntegerTable n) (j : ℕ) :
    t.toTable.lower j=t.lower j := by
  simp only [toTable,Table.lower,IntegerTable.lower,lowerNumerator,Array.getD,Array.size_map]
  split_ifs <;> simp

theorem IntegerTable.toTable_upper {n : ℕ} (t : IntegerTable n) (j : ℕ) :
    t.toTable.upper j=t.upper j := by
  simp only [toTable,Table.upper,IntegerTable.upper,upperNumerator,Array.getD,Array.size_map]
  split_ifs <;> simp

def leftFactor (a b j : ℕ) : ℤ := ((j+1)*(b-a):ℕ)
def rightFactor (n a j : ℕ) : ℤ := ((n-j)*a:ℕ)

def IntegerTable.Valid {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Prop :=
  0<a ∧ a<b ∧ 0<t.denominator ∧ t.pivot≤n ∧
  t.lowerValues.size=n+1 ∧ t.upperValues.size=n+1 ∧
  (t.lowerNumerator t.pivot:ℚ)≤t.denominator*seed n t.pivot ((a:ℚ)/b) ∧
  (t.denominator:ℚ)*seed n t.pivot ((a:ℚ)/b)≤t.upperNumerator t.pivot ∧
  ∀j:Fin n,if j.val<t.pivot then
    rightFactor n a j.val*t.lowerNumerator j.val≤leftFactor a b j.val*t.lowerNumerator (j.val+1) ∧
    leftFactor a b j.val*t.upperNumerator (j.val+1)≤rightFactor n a j.val*t.upperNumerator j.val
  else
    leftFactor a b j.val*t.lowerNumerator (j.val+1)≤rightFactor n a j.val*t.lowerNumerator j.val ∧
    rightFactor n a j.val*t.upperNumerator j.val≤leftFactor a b j.val*t.upperNumerator (j.val+1)
instance {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Decidable (t.Valid a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def IntegerTable.check {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Bool := decide (t.Valid a b)

theorem integer_edge_left (a b d j : ℕ) (v : ℤ) (hab : a≤b) (hb : 0<b) (hd : 0<d) :
    ((j+1:ℕ):ℚ)*(1-(a:ℚ)/b)*((v:ℚ)/d)=
      (leftFactor a b j:ℚ)*(v:ℚ)/((b:ℚ)*d) := by
  simp only [leftFactor]
  push_cast [Nat.cast_sub hab]
  have hb' : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd.ne'
  field_simp

theorem integer_edge_right (n a b d j : ℕ) (v : ℤ) (hb : 0<b) (hd : 0<d) :
    ((n-j:ℕ):ℚ)*((a:ℚ)/b)*((v:ℚ)/d)=
      (rightFactor n a j:ℚ)*(v:ℚ)/((b:ℚ)*d) := by
  simp only [rightFactor]
  push_cast
  have hb' : (b:ℚ)≠0 := by exact_mod_cast hb.ne'
  have hd' : (d:ℚ)≠0 := by exact_mod_cast hd.ne'
  field_simp

theorem IntegerTable.toTable_valid {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.Valid a b) : t.toTable.Valid ((a:ℚ)/b) := by
  have hb : 0<b := h.1.trans h.2.1
  have hb' : (0:ℚ)<b := by exact_mod_cast hb
  have ha' : (0:ℚ)<a := by exact_mod_cast h.1
  have hab' : (a:ℚ)<b := by exact_mod_cast h.2.1
  have hd : (0:ℚ)<t.denominator := by exact_mod_cast h.2.2.1
  refine ⟨div_pos ha' hb',(div_lt_one hb').mpr hab',h.2.2.2.1,?_,?_,?_,?_,?_⟩
  · simpa [toTable] using h.2.2.2.2.1
  · simpa [toTable] using h.2.2.2.2.2.1
  · rw [toTable_lower]
    apply (div_le_iff₀ hd).mpr
    simpa [toTable,mul_comm] using h.2.2.2.2.2.2.1
  · rw [toTable_upper]
    apply (le_div_iff₀ hd).mpr
    simpa [toTable,mul_comm] using h.2.2.2.2.2.2.2.1
  · intro j
    have he:=h.2.2.2.2.2.2.2.2 j
    simp only [toTable_lower,toTable_upper,lower,upper]
    dsimp only [toTable] at ⊢
    simp only [integer_edge_left a b t.denominator j.val _ h.2.1.le hb h.2.2.1,
      integer_edge_right n a b t.denominator j.val _ hb h.2.2.1]
    split_ifs with hj
    · rw [if_pos hj] at he
      constructor <;> apply (div_le_div_iff_of_pos_right (mul_pos hb' hd)).mpr
      · exact_mod_cast he.1
      · exact_mod_cast he.2
    · rw [if_neg hj] at he
      constructor <;> apply (div_le_div_iff_of_pos_right (mul_pos hb' hd)).mpr
      · exact_mod_cast he.1
      · exact_mod_cast he.2

theorem IntegerTable.check_sound {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.check a b=true) (j : ℕ) (hj : j≤n) :
    t.lower j≤FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b) ∧
    FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b)≤t.upper j := by
  have hv : t.Valid a b := of_decide_eq_true h
  simpa only [toTable_lower,toTable_upper] using Table.valid_sound (IntegerTable.toTable_valid hv) j hj

#print axioms IntegerTable.toTable_valid
#print axioms IntegerTable.check_sound
end ForestUnimodality.BinomialMassIntervalCertificate
