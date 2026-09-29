import ForestUnimodality.IndependentCountLaplace
import ForestUnimodality.BinomialGradientTable
import ForestUnimodality.BinomialGradientBound
import ForestUnimodality.BinomialGradientThirtyOne

/-! The complete two-threshold reciprocal envelope for the actual finite
layer distribution. Both bad-event corrections subtract the baseline already
paid by the same quadratic; neither is replaced by a full-event charge. -/
namespace ForestUnimodality.ReciprocalGradientBudget
open Finset KernelBudget

noncomputable def quadratic (a m x : ℝ) : ℝ :=
  1/m-(x-m)/m^2+(x-m)^2/(a*m^3)

theorem reciprocal_expansion {m x : ℝ} (hm : m≠0) (hx : x≠0) :
    1/x=1/m-(x-m)/m^2+(x-m)^2/(m^2*x) := by
  field_simp
  ring

theorem quadratic_ge_reciprocal {a m x : ℝ} (ha : 0<a) (hm : 0<m)
    (hx : a*m≤x) : 1/x≤quadratic a m x := by
  have hx0 : 0<x := (mul_pos ha hm).trans_le hx
  have he : quadratic a m x-1/x=(x-m)^2*(x-a*m)/(a*m^3*x) := by
    unfold quadratic
    field_simp
    ring
  have hh : 0≤(x-m)^2*(x-a*m)/(a*m^3*x) := by positivity
  linarith

theorem quadratic_ge_bad_baseline {a m x : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hm : 0<m) (hx : x≤a*m) : 1/(a*m)≤quadratic a m x := by
  have he : quadratic a m x-1/(a*m)=(x-a*m)*(x-2*m)/(a*m^3) := by
    unfold quadratic
    field_simp
    ring
  have hx2 : x≤2*m := by nlinarith
  have hh : 0≤(x-a*m)*(x-2*m)/(a*m^3) :=
    div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) (by positivity)
  linarith

theorem gradient_envelope {a a1 m v c0 c1 x f : ℝ}
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1) (hm : 0<m) (hv : 0<v)
    (hc0 : 0≤c0) (hc1 : 0≤c1)
    (hgood : a*m≤x → |f|≤c0/(v*x))
    (hmid : a1*m≤x → |f|≤c1/(v*x)) (hbad : |f|≤1) :
    |f|≤c0/v*quadratic a m x+
      ((c1/(v*a1)-c0/(v*a))/m)*(if x<a*m then 1 else 0)+
      ((m-c1/(v*a1))/m)*(if x<a1*m then 1 else 0) := by
  have ha0 := ha1.trans_le haa
  by_cases hx : x<a*m
  · rw [if_pos hx]
    have hq := mul_le_mul_of_nonneg_left
      (quadratic_ge_bad_baseline ha0 ha hm hx.le) (div_nonneg hc0 hv.le)
    have he : c0/v*(1/(a*m))=(c0/(v*a))/m := by ring
    rw [he] at hq
    by_cases hx1 : x<a1*m
    · rw [if_pos hx1]
      have he2 : c0/(v*a)/m+(c1/(v*a1)-c0/(v*a))/m+
          (m-c1/(v*a1))/m=1 := by field_simp; ring
      nlinarith
    · rw [if_neg hx1, mul_zero, add_zero, mul_one]
      have hxx : a1*m≤x := le_of_not_gt hx1
      have hxx0 : 0<x := (mul_pos ha1 hm).trans_le hxx
      have hh : c1/(v*x)≤c1/(v*(a1*m)) :=
        div_le_div_of_nonneg_left hc1 (by positivity) (mul_le_mul_of_nonneg_left hxx hv.le)
      have he2 : c1/(v*(a1*m))=(c1/(v*a1))/m := by ring
      rw [he2] at hh
      rw [sub_div]
      linarith [hmid hxx]
  · have hxx : a*m≤x := le_of_not_gt hx
    have hx1 : ¬x<a1*m := by nlinarith
    simp only [if_neg hx, if_neg hx1, mul_zero, add_zero]
    have hh := mul_le_mul_of_nonneg_left (quadratic_ge_reciprocal ha0 hm hxx)
      (div_nonneg hc0 hv.le)
    have he : c0/v*(1/x)=c0/(v*x) := by ring
    rw [he] at hh
    exact (hgood hxx).trans hh

theorem expect_quadratic {ι : Type*} (s : Finset ι) (w X : ι→ℝ)
    (hw : ∑x∈s,w x=1) {m : ℝ} (hmean : expect s w X=m) (a : ℝ) :
    expect s w (fun x=>quadratic a m (X x))=
      1/m+expect s w (fun x=>(X x-m)^2)/(a*m^3) := by
  have he : (fun x=>quadratic a m (X x))=
      (fun x=>1/m-(1/m^2)*(X x-m)+(1/(a*m^3))*(X x-m)^2) := by
    funext x; unfold quadratic; ring
  rw [he, expect_add, expect_sub, expect_const s w hw, expect_const_mul,
    expect_sub, expect_const s w hw, hmean, sub_self, mul_zero, sub_zero,
    expect_const_mul]
  ring

theorem abs_expect_le {ι : Type*} (s : Finset ι) (w f : ι→ℝ)
    (hw : ∀x∈s,0≤w x) : |expect s w f|≤expect s w (fun x=>|f x|) := by
  unfold KernelBudget.expect
  calc
    _ ≤ ∑x∈s,|w x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by apply sum_congr rfl; intro x hx; rw [abs_mul,abs_of_nonneg (hw x hx)]

/-- Exact two-event bound before a variance or Chernoff estimate is applied. -/
theorem expect_gradient_bound {ι : Type*} (s : Finset ι) (w X f : ι→ℝ)
    (hw : ∀x∈s,0≤w x) (hsum : ∑x∈s,w x=1)
    {a a1 m v c0 c1 : ℝ} (hmean : expect s w X=m)
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1) (hm : 0<m) (hv : 0<v)
    (hc0 : 0≤c0) (hc1 : 0≤c1)
    (hgood : ∀x∈s,0<w x → a*m≤X x → |f x|≤c0/(v*X x))
    (hmid : ∀x∈s,0<w x → a1*m≤X x → |f x|≤c1/(v*X x))
    (hbad : ∀x∈s,0<w x → |f x|≤1) :
    |expect s w f|≤c0/v*(1/m+expect s w (fun x=>(X x-m)^2)/(a*m^3))+
      ((c1/(v*a1)-c0/(v*a))/m)*expect s w (fun x=>if X x<a*m then 1 else 0)+
      ((m-c1/(v*a1))/m)*expect s w (fun x=>if X x<a1*m then 1 else 0) := by
  have hp := expect_le_of_positive_support s w (fun x=>|f x|)
    (fun x=>c0/v*quadratic a m (X x)+
      ((c1/(v*a1)-c0/(v*a))/m)*(if X x<a*m then 1 else 0)+
      ((m-c1/(v*a1))/m)*(if X x<a1*m then 1 else 0)) hw
    (fun x hx hwx=>gradient_envelope ha1 haa ha hm hv hc0 hc1
      (hgood x hx hwx) (hmid x hx hwx) (hbad x hx hwx))
  simp only [expect_add,expect_const_mul,expect_quadratic s w X hsum hmean] at hp
  exact (abs_expect_le s w f hw).trans hp


/-- Full finite-distribution form of (9.5), without square-root normalization. -/
theorem expect_gradient_bound_of_tail {ι : Type*} (s : Finset ι) (w X f : ι→ℝ)
    (hw : ∀x∈s,0≤w x) (hsum : ∑x∈s,w x=1)
    {a a1 m v c0 c1 D p0 p1 : ℝ} (hmean : expect s w X=m)
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1) (hm : 0<m) (hv : 0<v)
    (hc0 : 0≤c0) (hc1 : 0≤c1)
    (hA : c0/(v*a)≤c1/(v*a1)) (hAm : c1/(v*a1)≤m)
    (hvar : expect s w (fun x=>(X x-m)^2)≤D*m)
    (ht0 : expect s w (fun x=>if X x<a*m then 1 else 0)≤p0)
    (ht1 : expect s w (fun x=>if X x<a1*m then 1 else 0)≤p1)
    (hgood : ∀x∈s,0<w x → a*m≤X x → |f x|≤c0/(v*X x))
    (hmid : ∀x∈s,0<w x → a1*m≤X x → |f x|≤c1/(v*X x))
    (hbad : ∀x∈s,0<w x → |f x|≤1) :
    |expect s w f|≤c0/(v*m)*(1+D/(a*m))+
      ((c1/(v*a1)-c0/(v*a))/m)*p0+((m-c1/(v*a1))/m)*p1 := by
  have ha0 := ha1.trans_le haa
  have hmain : c0/v*(1/m+expect s w (fun x=>(X x-m)^2)/(a*m^3))≤
      c0/(v*m)*(1+D/(a*m)) := by
    calc
      _ ≤ c0/v*(1/m+(D*m)/(a*m^3)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (le_refl (1/m))
          (div_le_div_of_nonneg_right hvar (by positivity : 0≤a*m^3))) (div_nonneg hc0 hv.le)
      _ = _ := by field_simp
  have h0 := mul_le_mul_of_nonneg_left ht0 (div_nonneg (sub_nonneg.mpr hA) hm.le)
  have h1 := mul_le_mul_of_nonneg_left ht1 (div_nonneg (sub_nonneg.mpr hAm) hm.le)
  exact (expect_gradient_bound s w X f hw hsum hmean ha1 haa ha hm hv hc0 hc1
    hgood hmid hbad).trans (add_le_add (add_le_add hmain h0) h1)

theorem sqrt_mul_div_mean {m : ℝ} (hm : 0<m) (x : ℝ) :
    Real.sqrt m*(x/m)=x/Real.sqrt m := by
  field_simp [hm.ne',(Real.sqrt_pos.mpr hm).ne']
  linear_combination x*(Real.sq_sqrt hm.le)

theorem normalized_gradient_bound_of_tail {ι : Type*} (s : Finset ι) (w X f : ι→ℝ)
    (hw : ∀x∈s,0≤w x) (hsum : ∑x∈s,w x=1)
    {a a1 m v c0 c1 D p0 p1 : ℝ} (hmean : expect s w X=m)
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1) (hm : 0<m) (hv : 0<v)
    (hc0 : 0≤c0) (hc1 : 0≤c1)
    (hA : c0/(v*a)≤c1/(v*a1)) (hAm : c1/(v*a1)≤m)
    (hvar : expect s w (fun x=>(X x-m)^2)≤D*m)
    (ht0 : expect s w (fun x=>if X x<a*m then 1 else 0)≤p0)
    (ht1 : expect s w (fun x=>if X x<a1*m then 1 else 0)≤p1)
    (hgood : ∀x∈s,0<w x → a*m≤X x → |f x|≤c0/(v*X x))
    (hmid : ∀x∈s,0<w x → a1*m≤X x → |f x|≤c1/(v*X x))
    (hbad : ∀x∈s,0<w x → |f x|≤1) :
    Real.sqrt m*|expect s w f|≤c0/(v*Real.sqrt m)*(1+D/(a*m))+
      ((c1/(v*a1)-c0/(v*a))/Real.sqrt m)*p0+
      ((m-c1/(v*a1))/Real.sqrt m)*p1 := by
  have h := mul_le_mul_of_nonneg_left
    (expect_gradient_bound_of_tail s w X f hw hsum hmean ha1 haa ha hm hv hc0 hc1
      hA hAm hvar ht0 ht1 hgood hmid hbad) (Real.sqrt_nonneg m)
  have he : c0/(v*m)*(1+D/(a*m))=(c0/v*(1+D/(a*m)))/m := by ring
  rw [mul_add,mul_add,he,sqrt_mul_div_mean hm,←mul_assoc,sqrt_mul_div_mean hm,
    ←mul_assoc,sqrt_mul_div_mean hm] at h
  convert h using 2 <;> first | rfl | ring


noncomputable def gradient (d : ℕ) (j : ℤ) (q : ℝ) : ℝ :=
  binomialMass d (j+1) q-binomialMass d j q

theorem sum_binomialMass (d : ℕ) (q : ℝ) :
    (∑j∈range (d+1),binomialMass d (j:ℤ) q)=1 := by
  calc
    _ = (q+(1-q))^d := by
      rw [add_pow]
      apply sum_congr rfl
      intro j _
      rw [binomialMass_nat]
      ring
    _ = 1 := by simp

theorem binomialMass_le_one (d : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1) :
    binomialMass d j q≤1 := by
  by_cases hj : 0≤j ∧ j≤(d:ℤ)
  · have hmem : j.toNat∈range (d+1) := by simp only [mem_range]; omega
    have he : (j.toNat:ℤ)=j := by omega
    have h := Finset.single_le_sum (fun i (_:i∈range (d+1))=>binomialMass_nonneg d i hq0 hq1) hmem
    rw [sum_binomialMass,he] at h
    exact h
  · simp [binomialMass,hj]

theorem abs_gradient_le_one (d : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0≤q) (hq1 : q≤1) :
    |gradient d j q|≤1 := by
  have h0 := binomialMass_nonneg d j hq0 hq1
  have h1 := binomialMass_le_one d j hq0 hq1
  have h0' := binomialMass_nonneg d (j+1) hq0 hq1
  have h1' := binomialMass_le_one d (j+1) hq0 hq1
  exact abs_le.mpr ⟨by dsimp [gradient]; linarith,by dsimp [gradient]; linarith⟩

variable {V : Type*} [DecidableEq V]

theorem actual_gradient_eq_layer (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z : ℝ} (hz : 0<z) (k : ℕ) :
    tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1)-
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k=
    hardCoreLayerExpectation G S I z (fun j d=>gradient d ((k:ℤ)-j) (z/(1+z))) := by
  have he (j : ℕ) : ((k+1:ℕ):ℤ)-(j:ℤ)=((k:ℤ)-j)+1 := by omega
  rw [tiltedProbability_eq_binomial_mixture G S I hIS hI hz,
    tiltedProbability_eq_binomial_mixture G S I hIS hI hz]
  simp only [hardCoreLayerExpectation,gradient,he,mul_sub,sum_sub_distrib]

/-- The same true layer mean and variance are used for the main reciprocal
term and both strict lower-tail charges. Set p_i=exp(-m*rho_i) for (9.5).
Only the two displayed uniform binomial gradient constants remain inputs. -/
theorem hardCore_gradient_bound (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z : ℝ} (hz : 0<z) (k : ℕ)
    {a a1 v c0 c1 D p0 p1 : ℝ}
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1)
    (hm : 0<hardCoreAvailableMean G S I z) (hv : 0<v)
    (hc0 : 0≤c0) (hc1 : 0≤c1)
    (hA : c0/(v*a)≤c1/(v*a1)) (hAm : c1/(v*a1)≤hardCoreAvailableMean G S I z)
    (hvar : hardCoreAvailableVariance G S I z≤D*hardCoreAvailableMean G S I z)
    (ht0 : hardCoreAvailableLowerTail G S I z (a*hardCoreAvailableMean G S I z)≤p0)
    (ht1 : hardCoreAvailableLowerTail G S I z (a1*hardCoreAvailableMean G S I z)≤p1)
    (hgood : ∀d:ℕ,∀j:ℤ,a*hardCoreAvailableMean G S I z≤d →
      |gradient d j (z/(1+z))|≤c0/(v*d))
    (hmid : ∀d:ℕ,∀j:ℤ,a1*hardCoreAvailableMean G S I z≤d →
      |gradient d j (z/(1+z))|≤c1/(v*d)) :
    Real.sqrt (hardCoreAvailableMean G S I z)*
      |tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1)-
        tiltedProbability (countIndependent G S) z (partitionFunction G S z) k|≤
      c0/(v*Real.sqrt (hardCoreAvailableMean G S I z))*(1+D/(a*hardCoreAvailableMean G S I z))+
      ((c1/(v*a1)-c0/(v*a))/Real.sqrt (hardCoreAvailableMean G S I z))*p0+
      ((hardCoreAvailableMean G S I z-c1/(v*a1))/Real.sqrt (hardCoreAvailableMean G S I z))*p1 := by
  let Ω := range ((S\I).card+1) ×ˢ range (I.card+1)
  let w : ℕ×ℕ→ℝ := fun p=>hardCoreLayerWeight G S I z p.1 p.2
  let X : ℕ×ℕ→ℝ := fun p=>(p.2:ℝ)
  let f : ℕ×ℕ→ℝ := fun p=>gradient p.2 ((k:ℤ)-p.1) (z/(1+z))
  have hw : ∀p∈Ω,0≤w p := fun p _=>hardCoreLayerWeight_nonneg G S I hz.le p.1 p.2
  have hsum : ∑p∈Ω,w p=1 := by
    simpa only [Ω,w,sum_product] using sum_hardCoreLayerWeight G S I hIS hI hz.le
  have hmean : expect Ω w X=hardCoreAvailableMean G S I z := by
    simp only [KernelBudget.expect,Ω,w,X,sum_product,hardCoreAvailableMean]
  have hvar' : expect Ω w (fun p=>(X p-hardCoreAvailableMean G S I z)^2)≤
      D*hardCoreAvailableMean G S I z := by
    simpa only [hardCoreAvailableVariance,hardCoreLayerExpectation_eq_expect,Ω,w,X] using hvar
  have ht0' : expect Ω w (fun p=>if X p<a*hardCoreAvailableMean G S I z then 1 else 0)≤p0 := by
    simpa only [hardCoreAvailableLowerTail,hardCoreLayerExpectation_eq_expect,Ω,w,X] using ht0
  have ht1' : expect Ω w (fun p=>if X p<a1*hardCoreAvailableMean G S I z then 1 else 0)≤p1 := by
    simpa only [hardCoreAvailableLowerTail,hardCoreLayerExpectation_eq_expect,Ω,w,X] using ht1
  have hq0 : 0≤z/(1+z) := by positivity
  have hq1 : z/(1+z)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have h := normalized_gradient_bound_of_tail Ω w X f hw hsum hmean ha1 haa ha hm hv hc0 hc1
    hA hAm hvar' ht0' ht1' (fun p _ _=>hgood p.2 ((k:ℤ)-p.1))
    (fun p _ _=>hmid p.2 ((k:ℤ)-p.1)) (fun p _ _=>abs_gradient_le_one _ _ hq0 hq1)
  rw [actual_gradient_eq_layer G S I hIS hI hz,hardCoreLayerExpectation_eq_expect]
  exact h


/-- All profiles already have a proved all-binomial gradient bound. The two
table profiles impose only their displayed numerical activity and variance
conditions; the universal profile covers every q in (0,1). -/
inductive GradientProfile where
  | universal
  | thirtyOne
  | general (index : Fin 4)
  | near (index : Fin 4)

noncomputable def GradientProfile.constant : GradientProfile→ℝ
  | .universal => Real.pi/4
  | .thirtyOne => 31/100
  | .general i => BinomialGradientTable.generalConstant i
  | .near i => BinomialGradientTable.nearConstant i

def GradientProfile.Valid (P : GradientProfile) (q v threshold : ℝ) : Prop :=
  0<v ∧ v≤q*(1-q) ∧ 0<threshold ∧
    match P with
    | .universal => True
    | .thirtyOne => 3/10≤q ∧ q≤7/10
    | .general i => 3/10≤q ∧ q≤7/10 ∧ (BinomialGradientTable.scale i)^2≤threshold*v
    | .near i => 9/20≤q ∧ q≤11/20 ∧ (BinomialGradientTable.scale i)^2≤threshold*v

theorem GradientProfile.constant_nonneg (P : GradientProfile) : 0≤P.constant := by
  cases P with
  | universal => exact div_nonneg Real.pi_pos.le (by norm_num)
  | thirtyOne => norm_num [constant]
  | general i => fin_cases i <;> norm_num [constant,BinomialGradientTable.generalConstant]
  | near i => fin_cases i <;> norm_num [constant,BinomialGradientTable.nearConstant]

theorem GradientProfile.gradient_bound {P : GradientProfile} {q v threshold : ℝ}
    (h : P.Valid q v threshold) (d : ℕ) (j : ℤ) (hd : threshold≤d) :
    |gradient d j q|≤P.constant/(v*d) := by
  have hv := h.1
  have hvar := h.2.1
  have ht := h.2.2.1
  have hd0 : 0<(d:ℝ) := ht.trans_le hd
  have hdN : 0<d := by exact_mod_cast hd0
  have hqv : 0<q*(1-q) := hv.trans_le hvar
  have hden : v*d≤((d+1:ℕ):ℝ)*(q*(1-q)) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hvar hd0.le]
  have hth : threshold*v≤((d+1:ℕ):ℝ)*(q*(1-q)) :=
    (by nlinarith [mul_le_mul_of_nonneg_right hd hv.le] : threshold*v≤v*d).trans hden
  cases P with
  | universal =>
    have hg := BinomialGradientBound.binomial_gradient_bound d hdN j hqv
    change |gradient d j q|≤_ at hg
    have hg' : Real.pi/(4*(d:ℝ)*(q*(1-q)))=(Real.pi/4)/((d:ℝ)*(q*(1-q))) := by rw [div_div]; congr 1; ring
    rw [hg'] at hg
    apply hg.trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hvar hd0.le])
  | thirtyOne =>
    have hc := h.2.2.2
    have hg := BinomialGradientThirtyOne.gradient_bound_succ d j hc.1 hc.2
    apply hg.trans
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  | general i =>
    have hc := h.2.2.2
    have hg := BinomialGradientTable.general_gradient_bound i d (j+1) hc.1 hc.2.1
      (hc.2.2.trans hth)
    simp only [add_sub_cancel_right] at hg
    apply hg.trans
    exact div_le_div_of_nonneg_left (GradientProfile.constant_nonneg (.general i))
      (by positivity) hden
  | near i =>
    have hc := h.2.2.2
    have hg := BinomialGradientTable.near_gradient_bound i d (j+1) hc.1 hc.2.1
      (hc.2.2.trans hth)
    simp only [add_sub_cancel_right] at hg
    apply hg.trans
    exact div_le_div_of_nonneg_left (GradientProfile.constant_nonneg (.near i))
      (by positivity) hden

/-- (9.5) for the actual forest-layer distribution with both binomial
constants discharged by their analytic profile. Source variance and tail
estimates remain explicit true-distribution inputs. No independence of layer
coordinates or finite-binomial diagnostic is used. -/
theorem hardCore_gradient_bound_profiles (G : SimpleGraph V) (S I : Finset V)
    (hIS : I⊆S) (hI : G.IsIndepSet (I:Set V)) {z : ℝ} (hz : 0<z) (k : ℕ)
    (g0 g1 : GradientProfile) {a a1 v D p0 p1 : ℝ}
    (ha1 : 0<a1) (haa : a1≤a) (ha : a≤1)
    (hm : 0<hardCoreAvailableMean G S I z)
    (hgood : g0.Valid (z/(1+z)) v (a*hardCoreAvailableMean G S I z))
    (hmid : g1.Valid (z/(1+z)) v (a1*hardCoreAvailableMean G S I z))
    (hA : g0.constant/(v*a)≤g1.constant/(v*a1))
    (hAm : g1.constant/(v*a1)≤hardCoreAvailableMean G S I z)
    (hvar : hardCoreAvailableVariance G S I z≤D*hardCoreAvailableMean G S I z)
    (ht0 : hardCoreAvailableLowerTail G S I z (a*hardCoreAvailableMean G S I z)≤p0)
    (ht1 : hardCoreAvailableLowerTail G S I z (a1*hardCoreAvailableMean G S I z)≤p1) :
    Real.sqrt (hardCoreAvailableMean G S I z)*
      |tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k+1)-
        tiltedProbability (countIndependent G S) z (partitionFunction G S z) k|≤
      g0.constant/(v*Real.sqrt (hardCoreAvailableMean G S I z))*(1+D/(a*hardCoreAvailableMean G S I z))+
      ((g1.constant/(v*a1)-g0.constant/(v*a))/Real.sqrt (hardCoreAvailableMean G S I z))*p0+
      ((hardCoreAvailableMean G S I z-g1.constant/(v*a1))/Real.sqrt (hardCoreAvailableMean G S I z))*p1 :=
  hardCore_gradient_bound G S I hIS hI hz k ha1 haa ha hm hgood.1
    g0.constant_nonneg g1.constant_nonneg hA hAm hvar ht0 ht1
    (fun d j hd=>g0.gradient_bound hgood d j hd)
    (fun d j hd=>g1.gradient_bound hmid d j hd)

#print axioms reciprocal_expansion
#print axioms gradient_envelope
#print axioms normalized_gradient_bound_of_tail
#print axioms hardCore_gradient_bound
#print axioms GradientProfile.gradient_bound
#print axioms hardCore_gradient_bound_profiles
end ForestUnimodality.ReciprocalGradientBudget

