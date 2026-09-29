import ForestUnimodality.SpiderMean

/-! All-order path density from finite rational transfer witnesses. The
finite check establishes an invariant, rather than extrapolating samples. -/
namespace ForestUnimodality.ActivityPointDensity.Path

def data (x : ℚ) : ℕ→ℚ×ℚ×ℚ×ℚ
  | 0 => (1,0,1,0)
  | n+1 => let p:=data x n
           (p.1+x*p.2.2.1,p.2.1+x*p.2.2.2+x*p.2.2.1,p.1,p.2.1)

def Z (x : ℚ) (n : ℕ) : ℚ := (data x n).1
def M (x : ℚ) (n : ℕ) : ℚ := (data x n).2.1

theorem Z_rec (x : ℚ) (n : ℕ) : Z x (n+2)=Z x (n+1)+x*Z x n := rfl
theorem M_rec (x : ℚ) (n : ℕ) : M x (n+2)=M x (n+1)+x*M x n+x*Z x n := rfl

theorem Z_pos {x : ℚ} (hx : 0≤x) (n : ℕ) : 0<Z x n := by
  have hh : 0<(data x n).1 ∧ 0<(data x n).2.2.1 := by
    induction n with
    | zero => norm_num [data]
    | succ n ih =>
      refine ⟨?_,ih.1⟩
      exact add_pos_of_pos_of_nonneg ih.1 (mul_nonneg hx ih.2.le)
  exact hh.1

def Invariant (x r g L U : ℚ) (n : ℕ) : Prop :=
  Z x (n+1)≤U*Z x n ∧ L*Z x n≤Z x (n+1) ∧
  (r*(n:ℚ)+g)*Z x n≤M x n ∧
  (r*((n+1:ℕ):ℚ)+g)*Z x (n+1)≤M x (n+1)

instance (x r g L U : ℚ) (n : ℕ) : Decidable (Invariant x r g L U n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem invariant_step {x r g L U : ℚ}
    (hx : 0≤x) (hr : 0≤r) (hL : 1≤L) (hU : 1≤U)
    (hleft : L+x≤L*U) (hright : L*U≤U+x)
    (hbonus : r*U≤x*(1-2*r)) (n : ℕ) (h : Invariant x r g L U n) :
    Invariant x r g L U (n+1) := by
  obtain ⟨hu,hl,h0,h1⟩:=h
  have hz: 0≤Z x n := (Z_pos hx n).le
  have hupper : Z x (n+1)+x*Z x n≤U*Z x (n+1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hU),
      mul_nonneg hz (show 0≤L*U-L-x by linarith)]
  have hlower : L*Z x (n+1)≤Z x (n+1)+x*Z x n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hL),
      mul_nonneg hz (show 0≤U+x-L*U by linarith)]
  have hb : 0≤x*(1-2*r)*Z x n-r*Z x (n+1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hr,mul_nonneg (sub_nonneg.mpr hbonus) hz]
  unfold Invariant
  rw [show n+1+1=n+2 by omega,Z_rec,M_rec]
  refine ⟨hupper,hlower,h1,?_⟩
  push_cast at h1 ⊢
  linear_combination h1+x*h0+hb

structure Witness where
  start : ℕ
  L : ℚ
  U : ℚ

def Witness.Valid (w : Witness) (x r g : ℚ) (low : ℕ) : Prop :=
  0≤x ∧ 0≤r ∧ 1≤w.L ∧ 1≤w.U ∧ w.L+x≤w.L*w.U ∧ w.L*w.U≤w.U+x ∧
  r*w.U≤x*(1-2*r) ∧ low≤w.start ∧ Invariant x r g w.L w.U w.start ∧
  ∀n:Fin (w.start+2),low≤n.1 → (r*(n.1:ℚ)+g)*Z x n.1≤M x n.1

instance (w : Witness) (x r g : ℚ) (low : ℕ) : Decidable (w.Valid x r g low) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def Witness.check (w : Witness) (x r g : ℚ) (low : ℕ) : Bool := decide (w.Valid x r g low)

theorem Witness.check_sound {w : Witness} {x r g : ℚ} {low : ℕ}
    (h : w.check x r g low=true) : w.Valid x r g low := of_decide_eq_true h

theorem Witness.invariant_tail {w : Witness} {x r g : ℚ} {low : ℕ}
    (h : w.Valid x r g low) (n : ℕ) (hn : w.start≤n) : Invariant x r g w.L w.U n := by
  rcases h with ⟨hx,hr,hL,hU,hl,hu,hb,_,hbase,_⟩
  induction n,hn using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih => exact invariant_step hx hr hL hU hl hu hb n ih

theorem Witness.numerator_lower {w : Witness} {x r g : ℚ} {low : ℕ}
    (h : w.Valid x r g low) (n : ℕ) (hn : low≤n) : (r*(n:ℚ)+g)*Z x n≤M x n := by
  by_cases ht : w.start≤n
  · exact (Witness.invariant_tail h n ht).2.2.1
  · exact h.2.2.2.2.2.2.2.2.2 ⟨n,by omega⟩ hn

theorem Witness.mean_lower {w : Witness} {x r g : ℚ} {low : ℕ}
    (h : w.Valid x r g low) (n : ℕ) (hn : low≤n) :
    (r:ℝ)*(n:ℝ)+g≤(M x n:ℝ)/(Z x n:ℝ) := by
  have hz : (0:ℝ)<Z x n := by exact_mod_cast Z_pos h.1 n
  apply (le_div_iff₀ hz).mpr
  exact_mod_cast Witness.numerator_lower h n hn

theorem transfer (x : ℚ) (n : ℕ) :
    pathMomentTransfer (x:ℝ) n (1+x,x,1,0)=
      ((Z x (n+1):ℝ),(M x (n+1):ℝ),(Z x n:ℝ),(M x n:ℝ)) := by
  induction n with
  | zero => simp [pathMomentTransfer,Z,M,data]
  | succ n ih =>
    rw [pathMomentTransfer,ih]
    simp only [Z_rec,M_rec,Rat.cast_add,Rat.cast_mul]
    congr 2
    ring

variable {V : Type*} [DecidableEq V]

/-- A real graph path obeys the certified bound at every order, via its
actual partition function and first moment transfer. -/
theorem mean_lower_of_path {G : SimpleGraph V} {S : Finset V} {u v : V} {n : ℕ}
    (hp : PendantPathExtension G {v} v n S u) {w : Witness} {x r g : ℚ} {low : ℕ}
    (h : w.Valid x r g low) (hn : low≤S.card) :
    (r:ℝ)*(S.card:ℝ)+g≤hardCoreMean G S x := by
  have ht:=hp.moment_transfer (x:ℝ)
  rw [hardCore_singleton_statistics,transfer] at ht
  have hZ:=congrArg Prod.fst ht
  have hM:=congrArg (fun p:ℝ×ℝ×ℝ×ℝ=>p.2.1) ht
  dsimp only at hZ hM
  have hc : S.card=n+1 := by simpa [Nat.add_comm] using hp.card_eq
  unfold hardCoreMean
  rw [hZ,hM,hc]
  exact Witness.mean_lower h (n+1) (hc ▸ hn)

#print axioms invariant_step
#print axioms Witness.numerator_lower
#print axioms mean_lower_of_path
end ForestUnimodality.ActivityPointDensity.Path
