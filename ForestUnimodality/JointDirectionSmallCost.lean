import ForestUnimodality.JointDirectionScaling
import ForestUnimodality.JointDirectionEndpoint

namespace ForestUnimodality.JointDirectionSmallCost
open Real Finset JointDirectionBudget DirectionalSmallLayerBudget ReciprocalGradientBudget
open JointDirectionGraph JointDirectionScaling

noncomputable def cuts (m:ℝ) (i:ℕ) : ℝ := ((i:ℝ)+1)/54*m
noncomputable def bound (p:Parameters) (m:ℝ) : ℝ :=
  exp (-p.smallRate 0*m)+(1/(p.v*m))*(p.smallCoefficient 22*exp (-p.smallRate 23*m)+
    ∑i∈range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*exp (-p.smallRate (i+1)*m))

theorem cuts_start {m:ℝ} (hm:0<m) : 0<cuts m 0 := by unfold cuts;positivity
theorem cuts_steps {m:ℝ} (hm:0≤m) (i:ℕ) : cuts m i≤cuts m (i+1) := by
  unfold cuts
  push_cast
  nlinarith
theorem cuts_end (m:ℝ) : cuts m 23=(4/9)*m := by norm_num [cuts]

theorem price_eq (p:Parameters) (P:ℕ→GradientProfile) {m:ℝ} (hm:0<m)
    (hconstant:∀i<23,(P i).constant=p.smallCoefficient i*(((i:ℝ)+1)/54))
    (i:ℕ) (hi:i<23) : price p.v (cuts m) P i=p.smallCoefficient i/(p.v*m) := by
  unfold price cuts
  rw [hconstant i hi]
  have hc : (i:ℝ)+1≠0 := by positivity
  field_simp

theorem bound_nonneg (p:Parameters) (hp:Valid p) {m:ℝ} (hm:0<m) : 0≤bound p m := by
  rcases hp with ⟨hs,hv,hV,heta,hD,hR,hamp,hlf,hA,hB,hprice,ham,hthreshold,hprofile,hsmall,hsmall0,hC,hCdec⟩
  unfold bound
  apply add_nonneg (exp_pos _).le
  apply mul_nonneg (by positivity)
  apply add_nonneg (mul_nonneg (hC 22 (by norm_num)) (exp_pos _).le)
  apply sum_nonneg
  intro i hi
  exact mul_nonneg (sub_nonneg.mpr (hCdec i (mem_range.mp hi))) (exp_pos _).le

theorem small_eq (p:Parameters) {m:ℝ} (hm:0<m) :
    small p m=p.amp*sqrt (2*Real.pi*p.V)*sqrt m*bound p m := by
  rw [JointDirectionEndpoint.small_eq_sqrt p hm]
  unfold JointDirectionEndpoint.smallSqrt bound
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  field_simp
  rw [sq_sqrt hm.le]

theorem cost_normalized (p:Parameters) (hp:Valid p) {m vq r:ℝ}
    (hm:0<m) (hvq:0<vq) (hV:vq≤p.V) (_hr:0≤r) (hr1:r<1)
    (hamp:r/(1-r)≤p.amp) :
    r*bound p m≤normalizer vq m*(1-r)*small p m := by
  have hb:=bound_nonneg p hp hm
  have hamp0:=hp.2.2.2.2.2.2.1
  have hd:0<1-r:=sub_pos.mpr hr1
  have ha : r≤p.amp*(1-r) := (div_le_iff₀ hd).mp hamp
  have hn:=mul_le_mul_of_nonneg_right (normalizer_lower hvq hm hV) (sqrt_nonneg m)
  have hs : sqrt m≠0 := (sqrt_pos.mpr hm).ne'
  have hn' : 1≤normalizer vq m*sqrt (2*Real.pi*p.V)*sqrt m := by
    simpa only [one_div,inv_mul_cancel₀ hs] using hn
  have he:=mul_le_mul_of_nonneg_right hn' (mul_nonneg (mul_nonneg hamp0 hd.le) hb)
  have he':=mul_le_mul_of_nonneg_right ha hb
  rw [small_eq p hm]
  nlinarith

variable {V:Type*} [DecidableEq V]
theorem actual_bound (p:Parameters) (hp:Valid p) (G:SimpleGraph V) (S I:Finset V)
    {z m:ℝ} (hz:0≤z) (hm:0<m) (P:ℕ→GradientProfile)
    (hconstant:∀i<23,(P i).constant=p.smallCoefficient i*(((i:ℝ)+1)/54))
    (htail:∀i<24,hardCoreAvailableLowerTail G S I z (cuts m i)≤exp (-p.smallRate i*m)) :
    hardCoreLayerExpectation G S I z (fun _ M=>badCost p.v (cuts m) P 22 M)≤bound p m := by
  have hv:=hp.2.1
  have hCdec:=hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hprice:∀i<22,price p.v (cuts m) P (i+1)≤price p.v (cuts m) P i := by
    intro i hi
    rw [price_eq p P hm hconstant (i+1) (by omega),price_eq p P hm hconstant i (by omega)]
    exact div_le_div_of_nonneg_right (hCdec i hi) (mul_pos hv hm).le
  have he:=bad_cost_cumulative G S I hz hv (cuts m) (fun i=>exp (-p.smallRate i*m)) P 22
    (cuts_start hm) (fun i _=>cuts_steps hm.le i) hprice (fun i hi=>htail i (by omega))
  apply he.trans_eq
  rw [price_eq p P hm hconstant 22 (by omega)]
  have hsum : (∑i∈range 22,(price p.v (cuts m) P i-price p.v (cuts m) P (i+1))*exp (-p.smallRate (i+1)*m))=
      (1/(p.v*m))*∑i∈range 22,(p.smallCoefficient i-p.smallCoefficient (i+1))*exp (-p.smallRate (i+1)*m) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi':=mem_range.mp hi
    rw [price_eq p P hm hconstant i (by omega),price_eq p P hm hconstant (i+1) (by omega)]
    ring
  rw [hsum]
  unfold bound
  ring

#print axioms small_eq
#print axioms cost_normalized
#print axioms actual_bound
end ForestUnimodality.JointDirectionSmallCost
