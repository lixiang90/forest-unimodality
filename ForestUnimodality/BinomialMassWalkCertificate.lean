import ForestUnimodality.BinomialMassExactIntegerCertificate

/-! Linear list traversal for the adjacent interval checks. The existing
array tables remain the public data representation. -/
namespace ForestUnimodality.BinomialMassIntervalCertificate

def Edge (n p a b j : ℕ) (l u ln un : ℤ) : Prop :=
  if j<p then rightFactor n a j*l≤leftFactor a b j*ln ∧ leftFactor a b j*un≤rightFactor n a j*u
  else leftFactor a b j*ln≤rightFactor n a j*l ∧ rightFactor n a j*u≤leftFactor a b j*un
instance (n p a b j : ℕ) (l u ln un : ℤ) : Decidable (Edge n p a b j l u ln un) := by
  unfold Edge
  infer_instance

def walk (n p a b : ℕ) : ℕ→List ℤ→List ℤ→Bool
  | j,l::ln::ls,u::un::us => decide (Edge n p a b j l u ln un) && walk n p a b (j+1) (ln::ls) (un::us)
  | _,_,_ => true

theorem walk_sound (n p a b : ℕ) (ls us : List ℤ) (j k : ℕ)
    (h : walk n p a b j ls us=true) (hl : k+1<ls.length) (hu : k+1<us.length) :
    Edge n p a b (j+k) (ls.getD k 0) (us.getD k 0) (ls.getD (k+1) 0) (us.getD (k+1) 0) := by
  induction ls generalizing us j k with
  | nil => simp at hl
  | cons l ls ih =>
    cases ls with
    | nil => simp at hl
    | cons ln ls =>
      cases us with
      | nil => simp at hu
      | cons u us =>
        cases us with
        | nil => simp at hu
        | cons un us =>
          have hh : decide (Edge n p a b j l u ln un)=true ∧
              walk n p a b (j+1) (ln::ls) (un::us)=true := by
            simpa only [walk,Bool.and_eq_true] using h
          cases k with
          | zero =>
            simpa only [Nat.add_zero,List.getD_cons_zero,List.getD_cons_succ] using (of_decide_eq_true hh.1)
          | succ k =>
            have hi:=ih (un::us) (j+1) k hh.2 (by simpa using hl) (by simpa using hu)
            rw [show j+1+k=j+(k+1) by omega] at hi
            simpa only [Nat.succ_eq_add_one,List.getD_cons_succ] using hi

theorem array_getD_toList (vs : Array ℤ) (j : ℕ) : vs.toList.getD j 0=vs.getD j 0 := by
  by_cases hj:j<vs.size
  · simp [Array.getD,hj,List.getD_eq_getElem?_getD]
  · simp [Array.getD,hj,List.getD_eq_getElem?_getD]

def IntegerTable.WalkValid {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Prop :=
  0<a ∧ a<b ∧ 0<t.denominator ∧ t.pivot≤n ∧
  t.lowerValues.size=n+1 ∧ t.upperValues.size=n+1 ∧
  t.lowerNumerator t.pivot*(b^n:ℕ)≤t.pivotNumerator a b ∧
  t.pivotNumerator a b≤t.upperNumerator t.pivot*(b^n:ℕ) ∧
  walk n t.pivot a b 0 t.lowerValues.toList t.upperValues.toList=true
instance {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Decidable (t.WalkValid a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
def IntegerTable.walkCheck {n : ℕ} (t : IntegerTable n) (a b : ℕ) : Bool := decide (t.WalkValid a b)

theorem IntegerTable.walkValid_exactValid {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.WalkValid a b) : t.ExactValid a b := by
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,?_⟩
  intro j
  have hh:=walk_sound n t.pivot a b t.lowerValues.toList t.upperValues.toList 0 j.val
    h.2.2.2.2.2.2.2.2 (by simp [h.2.2.2.2.1]) (by simp [h.2.2.2.2.2.1])
  simpa only [Nat.zero_add,array_getD_toList,Edge,lowerNumerator,upperNumerator] using hh

theorem IntegerTable.walkCheck_sound {n : ℕ} {t : IntegerTable n} {a b : ℕ}
    (h : t.walkCheck a b=true) (j : ℕ) (hj : j≤n) :
    t.lower j≤FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b) ∧
    FiniteKernelRationalCertificate.mass n (j:ℤ) ((a:ℚ)/b)≤t.upper j := by
  have hv : t.WalkValid a b := of_decide_eq_true h
  simpa only [toTable_lower,toTable_upper] using Table.valid_sound
    (IntegerTable.toTable_valid (IntegerTable.exactValid_valid (IntegerTable.walkValid_exactValid hv))) j hj

#print axioms walk_sound
#print axioms IntegerTable.walkCheck_sound
end ForestUnimodality.BinomialMassIntervalCertificate

