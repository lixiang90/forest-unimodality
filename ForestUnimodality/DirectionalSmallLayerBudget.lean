import ForestUnimodality.ReciprocalGradientBudget
import ForestUnimodality.NegativePowerLayerBudget

/-! The discarded free-count layers pay a signed gradient only. Prices are
charged cumulatively across disjoint slices under the same actual layer law. -/
namespace ForestUnimodality.DirectionalSmallLayerBudget
open Finset ReciprocalGradientBudget NegativePowerLayerBudget

noncomputable def signedMass (reverse : Bool) (M : ℕ) (q r : ℝ) (k : ℤ) : ℝ :=
  binomialMass M k q-r*binomialMass M (if reverse then k-1 else k+1) q

def edgeIndex (reverse : Bool) (k : ℤ) : ℤ := if reverse then k-1 else k

theorem signedMass_ge_gradient (reverse : Bool) (M : ℕ) (k : ℤ) {q r C : ℝ}
    (hq0 : 0≤q) (hq1 : q≤1) (hr : 0≤r) (hr1 : r≤1)
    (hgrad : |gradient M (edgeIndex reverse k) q|≤C) :
    -r*C≤signedMass reverse M q r k := by
  have hb:=binomialMass_nonneg M k hq0 hq1
  have hm:=mul_nonneg (sub_nonneg.mpr hr1) hb
  have hlo:=mul_le_mul_of_nonneg_left (abs_le.mp hgrad).1 hr
  have hhi:=mul_le_mul_of_nonneg_left (abs_le.mp hgrad).2 hr
  cases reverse <;> simp only [edgeIndex,Bool.false_eq_true,if_false,if_true,
    gradient,signedMass,sub_add_cancel] at hlo hhi ⊢ <;> nlinarith

noncomputable def price (v : ℝ) (cuts : ℕ→ℝ) (P : ℕ→GradientProfile) (i : ℕ) : ℝ :=
  (P i).constant/(v*cuts i)

noncomputable def badCost (v : ℝ) (cuts : ℕ→ℝ) (P : ℕ→GradientProfile) (n M : ℕ) : ℝ :=
  (if (M:ℝ)<cuts 0 then 1 else 0)+
    ∑i∈range (n+1),price v cuts P i*
      (if cuts i≤(M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0)

theorem price_nonneg {v : ℝ} (hv : 0<v) (cuts : ℕ→ℝ)
    (P : ℕ→GradientProfile) {i : ℕ} (hi : 0<cuts i) : 0≤price v cuts P i := by
  exact div_nonneg (P i).constant_nonneg (mul_pos hv hi).le

theorem badCost_nonneg {v : ℝ} (hv : 0<v) (cuts : ℕ→ℝ)
    (P : ℕ→GradientProfile) (n M : ℕ) (hcuts : ∀i≤n,0<cuts i) :
    0≤badCost v cuts P n M := by
  apply add_nonneg (by split_ifs <;> norm_num)
  exact sum_nonneg (fun i hi=>mul_nonneg (price_nonneg hv cuts P (hcuts i (by
    have:=mem_range.mp hi;omega))) (by split_ifs <;> norm_num))

theorem bad_gradient_bound (M : ℕ) (j : ℤ) {q v : ℝ}
    (hq0 : 0≤q) (hq1 : q≤1) (hv : 0<v)
    (cuts : ℕ→ℝ) (P : ℕ→GradientProfile) (n : ℕ)
    (hstart : 0<cuts 0) (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hP : ∀i≤n,(P i).Valid q v (cuts i)) (hbad : (M:ℝ)<cuts (n+1)) :
    |gradient M j q|≤badCost v cuts P n M := by
  have hc (i:ℕ) (hi:i≤n+1) : 0<cuts i := hstart.trans_le
    (cut_le_of_steps cuts n hsteps (Nat.zero_le i) hi)
  have hterm (i:ℕ) (hi:i∈range (n+1)) : 0≤price v cuts P i*
      (if cuts i≤(M:ℝ) ∧ (M:ℝ)<cuts (i+1) then 1 else 0) := by
    exact mul_nonneg (price_nonneg hv cuts P (hc i (by have:=mem_range.mp hi;omega)))
      (by split_ifs <;> norm_num)
  have hsum:=sum_nonneg hterm
  by_cases hb : (M:ℝ)<cuts 0
  · exact (abs_gradient_le_one M j hq0 hq1).trans (by
      simpa only [badCost,if_pos hb] using (le_add_of_nonneg_right hsum : (1:ℝ)≤1+_))
  · obtain ⟨i,hi,hlo,hhi⟩:=exists_cut_interval cuts n (le_of_not_gt hb) hbad
    have hp:=GradientProfile.gradient_bound (hP i hi) M j hlo
    have hprice : (P i).constant/(v*(M:ℝ))≤price v cuts P i := by
      apply div_le_div_of_nonneg_left (P i).constant_nonneg (mul_pos hv (hc i (by omega)))
      exact mul_le_mul_of_nonneg_left hlo hv.le
    have hsingle:=single_le_sum hterm (mem_range.mpr (by omega : i<n+1))
    simp only [if_pos (And.intro hlo hhi),mul_one] at hsingle
    apply (hp.trans hprice).trans
    simpa only [badCost,if_neg hb,zero_add] using hsingle

variable {V : Type*} [DecidableEq V]

theorem whole_direction_ge_retained (G : SimpleGraph V) (S I : Finset V)
    {z q v r : ℝ} (hz : 0≤z) (hq0 : 0≤q) (hq1 : q≤1) (hv : 0<v)
    (hr : 0≤r) (hr1 : r≤1) (cuts : ℕ→ℝ) (P : ℕ→GradientProfile) (n : ℕ)
    (hstart : 0<cuts 0) (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hP : ∀i≤n,(P i).Valid q v (cuts i)) (reverse : Bool) (k : ℤ) :
    hardCoreLayerExpectation G S I z (fun j M=>if cuts (n+1)≤(M:ℝ) then
      signedMass reverse M q r (k-j) else 0)-
      r*hardCoreLayerExpectation G S I z (fun _ M=>badCost v cuts P n M)≤
    hardCoreLayerExpectation G S I z (fun j M=>signedMass reverse M q r (k-j)) := by
  rw [←layer_const_mul,←layer_sub]
  apply layer_mono G S I hz
  intro j M
  by_cases hgood : cuts (n+1)≤(M:ℝ)
  · simp only [if_pos hgood]
    have hc (i:ℕ) (hi:i≤n) : 0<cuts i := hstart.trans_le
      (cut_le_of_steps cuts n hsteps (Nat.zero_le i) (by omega))
    exact sub_le_self _ (mul_nonneg hr (badCost_nonneg hv cuts P n M hc))
  · simp only [if_neg hgood,zero_sub]
    simpa only [neg_mul] using signedMass_ge_gradient reverse M (k-j) hq0 hq1 hr hr1
      (bad_gradient_bound M (edgeIndex reverse (k-j)) hq0 hq1 hv cuts P n hstart hsteps hP
        (lt_of_not_ge hgood))

theorem bad_cost_layer_eq (G : SimpleGraph V) (S I : Finset V) (z v : ℝ)
    (cuts : ℕ→ℝ) (P : ℕ→GradientProfile) (n : ℕ) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost v cuts P n M)=
      hardCoreAvailableLowerTail G S I z (cuts 0)+
      ∑i∈range (n+1),price v cuts P i*hardCoreAvailableSlice G S I z (cuts i) (cuts (i+1)) := by
  unfold badCost
  rw [layer_add,layer_sum]
  simp only [layer_const_mul,hardCoreAvailableLowerTail,hardCoreAvailableSlice]

theorem bad_cost_cumulative (G : SimpleGraph V) (S I : Finset V) {z v : ℝ}
    (hz : 0≤z) (hv : 0<v) (cuts bound : ℕ→ℝ) (P : ℕ→GradientProfile) (n : ℕ)
    (hstart : 0<cuts 0) (hsteps : ∀i≤n,cuts i≤cuts (i+1))
    (hprice : ∀i<n,price v cuts P (i+1)≤price v cuts P i)
    (hbound : ∀i≤n+1,hardCoreAvailableLowerTail G S I z (cuts i)≤bound i) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost v cuts P n M)≤
      bound 0+price v cuts P n*bound (n+1)+
      ∑i∈range n,(price v cuts P i-price v cuts P (i+1))*bound (i+1) := by
  rw [bad_cost_layer_eq]
  have hc : 0<cuts n := hstart.trans_le
    (cut_le_of_steps cuts n hsteps (Nat.zero_le n) (by omega))
  have h:=hardCoreAvailableSlices_le_cumulative G S I hz cuts (price v cuts P) bound n hsteps
    (price_nonneg hv cuts P hstart) (price_nonneg hv cuts P hc) hprice
    (fun i hi=>hbound (i+1) (by omega))
  have h0:=hbound 0 (by omega)
  linarith

#print axioms whole_direction_ge_retained
#print axioms bad_cost_cumulative
end ForestUnimodality.DirectionalSmallLayerBudget
