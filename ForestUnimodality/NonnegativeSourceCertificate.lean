import ForestUnimodality.SourceGeneralCapacity

/-! The arbitrary nonnegative-mark source inequality, with a semantic
reduction from one continuous scalar certificate to the actual forest law. -/
namespace ForestUnimodality
open Finset Filter Set
open scoped Topology

noncomputable def nonnegativeSourceEta (b p : ℝ) : ℝ :=
  1/((1+b*(1-p))*sourceOddsCapacity b (sourceLogCapacity b p))

noncomputable def nonnegativeSourceHomogeneous (b A u v p a d : ℝ) : ℝ :=
  A*a^2/p+nonnegativeSourceEta b p*(a-d)^2-(1-p)*d^2+
  u*((1/(p*sourceLogCapacity b p))*(max 0 (a-d))^2-(1-p/2)*(max 0 d)^2)+
  v*((1/(p*sourceLogCapacity b p))*(max 0 (d-a))^2-(1-p/2)*(max 0 (-d))^2)

def NonnegativeSourceRowValid (b A u v : ℝ) : Prop :=
  ∀ p z : ℝ, 0<p → p≤b/(1+b) → (p=b/(1+b) → z=1) →
    0≤nonnegativeSourceHomogeneous b A u v p 1 z

theorem nonnegativeSourceHomogeneous_scale {b A u v p a d : ℝ} (ha : 0<a) :
    nonnegativeSourceHomogeneous b A u v p a d =
      a^2*nonnegativeSourceHomogeneous b A u v p 1 (d/a) := by
  have hmax (x : ℝ) : max 0 (x/a)=max 0 x/a := by
    simpa only [zero_div] using max_div_div_right ha.le 0 x
  have h₁ : 1-d/a=(a-d)/a := by field_simp
  have h₂ : d/a-1=(d-a)/a := by field_simp
  have h₃ : -(d/a)=(-d)/a := by ring
  simp only [nonnegativeSourceHomogeneous, h₁, h₂, h₃, hmax]
  field_simp [ha.ne']

/-- Zero marks follow by continuity of the homogeneous expression, while
the leaf endpoint uses its actual response d=a. -/
theorem NonnegativeSourceRowValid.homogeneous {b A u v : ℝ}
    (h : NonnegativeSourceRowValid b A u v) {p a d : ℝ}
    (hp : 0<p) (hpq : p≤b/(1+b)) (ha : 0≤a) (hend : p=b/(1+b) → d=a) :
    0≤nonnegativeSourceHomogeneous b A u v p a d := by
  have hpos (a : ℝ) (ha : 0<a) (he : p=b/(1+b) → d=a) :
      0≤nonnegativeSourceHomogeneous b A u v p a d := by
    rw [nonnegativeSourceHomogeneous_scale ha]
    exact mul_nonneg (sq_nonneg a) (h p (d/a) hp hpq (fun hq => by rw [he hq]; exact div_self ha.ne'))
  by_cases ha0 : a=0
  · subst a
    by_cases he : p=b/(1+b)
    · have hd := hend he
      simp [hd, nonnegativeSourceHomogeneous]
    · have hf : ContinuousAt (fun t : ℝ => nonnegativeSourceHomogeneous b A u v p t d) 0 := by
        unfold nonnegativeSourceHomogeneous
        fun_prop
      apply ge_of_tendsto (hf.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hpos t ht (fun hpq => False.elim (he hpq))
  · exact hpos a (lt_of_le_of_ne ha (Ne.symm ha0)) hend

variable {V : Type*} [DecidableEq V]

/-- Keeping the actual parent debit produces the eta-weighted blocking
inequality; arbitrary branching and signed responses remain allowed. -/
theorem SourceMessages.nonnegative_source_blocking {G : SimpleGraph V} {S : Finset V}
    {activity a : V → ℝ} {parent : V → Option V} {p d : V → ℝ}
    (h : SourceMessages G S activity a parent p d) {b : ℝ}
    (hactivity : ∀x∈S, 0<activity x ∧ activity x≤b) :
    (∑x∈S, p x*nonnegativeSourceEta b (p x)*(a x-d x)^2) ≤
      ∑x∈S, (p x-heterogeneousMarginal G S activity x)*(1-p x)*d x^2 := by
  have hlocal : (∑x∈S, p x*nonnegativeSourceEta b (p x)*(a x-d x)^2) ≤
      ∑x∈S, heterogeneousMarginal G S activity x*
        ((a x-d x)^2/sourceOddsCapacity b (sourceLogCapacity b (p x))) := by
    apply sum_le_sum
    intro x hx
    have hp := h.probability_pos (fun y hy => (hactivity y hy).1) hx
    have hp1 := (h.probability x hx).2
    have hb := (hactivity x hx).1.trans_le (hactivity x hx).2
    have hden : 0<1+b*(1-p x) := by nlinarith [mul_pos hb (sub_pos.mpr hp1)]
    have hr := (h.retention_bounds hactivity hx).1
    have hpi : p x/(1+b*(1-p x))≤heterogeneousMarginal G S activity x := by
      have hm := mul_le_mul_of_nonneg_right hr hp.le
      simpa only [one_div_mul_eq_div, div_mul_cancel₀ _ hp.ne'] using hm
    have hcap := h.child_odds_capacity hactivity hx
    have hH : 0≤sourceOddsCapacity b (sourceLogCapacity b (p x)) := by
      apply le_trans ?_ hcap
      exact sum_nonneg (fun y hy => div_nonneg (h.probability y (mem_filter.mp hy).1).1
        (sub_nonneg.mpr (h.probability y (mem_filter.mp hy).1).2.le))
    have hh := mul_le_mul_of_nonneg_right hpi (div_nonneg (sq_nonneg (a x-d x)) hH)
    convert hh using 1
    simp only [nonnegativeSourceEta, div_eq_mul_inv, mul_inv_rev]
    ring
  have hb := h.blocking_capacity_budget hactivity
  rw [sum_sub_distrib] at hb
  exact hlocal.trans (sub_nonpos.mp hb)

theorem forest_nonnegative_source_variance_pos
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (activity a : V→ℝ)
    {b A u v : ℝ} (hactivity : ∀x∈S, 0<activity x ∧ activity x≤b)
    (ha : ∀x∈S, 0≤a x) (hu : 0≤u) (hv : 0≤v)
    (hvalid : NonnegativeSourceRowValid b A u v) :
    heterogeneousVariance G S activity (markedSum a)≤A*(∑x∈S, a x^2) := by
  obtain ⟨parent,p,d,hm,hmean,hvar⟩ := exists_forest_source_messages_moments G hG S activity a
    (fun x hx => (hactivity x hx).1.le)
  have hp : ∀x∈S, 0<p x := fun x hx => hm.probability_pos (fun y hy => (hactivity y hy).1) hx
  have hrows : 0≤∑x∈S, p x*nonnegativeSourceHomogeneous b A u v (p x) (a x) (d x) := by
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (hp x hx).le (hvalid.homogeneous (hp x hx)
      (hm.probability_le_bound hactivity hx) (ha x hx) (hm.response_at_probability_endpoint hactivity hx))
  have hpos := hm.positive_capacity_budget_scaled hactivity (fun _=>u) (fun _=>hu)
  have hneg := hm.negative_capacity_budget_scaled hactivity (fun _=>v) (fun _=>hv)
  have hblock := hm.nonnegative_source_blocking hactivity
  have he : (∑x∈S, p x*nonnegativeSourceHomogeneous b A u v (p x) (a x) (d x)) =
      A*(∑x∈S, a x^2)+(∑x∈S, p x*nonnegativeSourceEta b (p x)*(a x-d x)^2)-
      (∑x∈S, p x*(1-p x)*d x^2)+sourcePositiveCapacityBudget S a parent p d b (fun _=>u)+
      sourceNegativeCapacityBudget S a parent p d b (fun _=>v) := by
    simp only [sourcePositiveCapacityBudget, sourceNegativeCapacityBudget, ← sum_add_distrib,
      ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro x hx
    unfold nonnegativeSourceHomogeneous
    field_simp [(hp x hx).ne']
  have hvardiff : (∑x∈S, p x*(1-p x)*d x^2)-
      (∑x∈S, (p x-heterogeneousMarginal G S activity x)*(1-p x)*d x^2) =
      heterogeneousVariance G S activity (markedSum a) := by
    rw [hvar, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x _
    ring
  linarith

theorem continuousAt_heterogeneousVariance (G : SimpleGraph V) (S : Finset V)
    (activity : ℝ→V→ℝ) (f : Finset V→ℝ) {t₀ : ℝ}
    (hc : ∀x, ContinuousAt (fun t=>activity t x) t₀)
    (hbase : ∀x∈S, 0≤activity t₀ x) :
    ContinuousAt (fun t=>heterogeneousVariance G S (activity t) f) t₀ := by
  have hw (J : Finset V) : ContinuousAt (fun t=>heterogeneousWeight (activity t) J) t₀ := by
    unfold heterogeneousWeight
    fun_prop
  have htotal : ContinuousAt (fun t=>FiniteTilt.total (independentSubsets G S)
      (heterogeneousWeight (activity t))) t₀ := by
    unfold FiniteTilt.total
    fun_prop
  have hZ : FiniteTilt.total (independentSubsets G S) (heterogeneousWeight (activity t₀))≠0 :=
    (heterogeneousPartition_pos G S (activity t₀) hbase).ne'
  have hmean (g : Finset V→ℝ) : ContinuousAt (fun t=>heterogeneousMean G S (activity t) g) t₀ := by
    exact (show ContinuousAt (fun t=>FiniteTilt.numerator (independentSubsets G S)
      (heterogeneousWeight (activity t)) g) t₀ by unfold FiniteTilt.numerator; fun_prop).div htotal hZ
  exact (hmean (fun J=>f J*f J)).sub ((hmean f).mul (hmean f))

/-- Zero activities are obtained as a limit inside the same finite hard-core
law; no vertex with zero activity is assumed to have positive probability. -/
theorem forest_nonnegative_source_variance
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (activity a : V→ℝ)
    {b A u v : ℝ} (hb : 0<b) (hactivity : ∀x∈S, 0≤activity x ∧ activity x≤b)
    (ha : ∀x∈S, 0≤a x) (hu : 0≤u) (hv : 0≤v)
    (hvalid : NonnegativeSourceRowValid b A u v) :
    heterogeneousVariance G S activity (markedSum a)≤A*(∑x∈S, a x^2) := by
  let activityPath := fun t : ℝ => fun x : V => (1-t)*activity x+t*b
  have hbase : activityPath 0=activity := by funext x; simp [activityPath]
  have hcont := continuousAt_heterogeneousVariance G S activityPath (markedSum a)
    (t₀:=0) (fun x=>by dsimp [activityPath]; fun_prop) (fun x hx=>by simpa [activityPath] using (hactivity x hx).1)
  have htend := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  rw [hbase] at htend
  apply le_of_tendsto htend
  have hsmall : ∀ᶠt in 𝓝[>] (0:ℝ), t<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht ht1
  apply forest_nonnegative_source_variance_pos G hG S (activityPath t) a ?_ ha hu hv hvalid
  intro x hx
  dsimp [activityPath]
  have hnonneg := mul_nonneg (sub_nonneg.mpr ht1.le) (hactivity x hx).1
  have hpos := mul_pos ht hb
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hactivity x hx).2)]

#print axioms NonnegativeSourceRowValid.homogeneous
#print axioms SourceMessages.nonnegative_source_blocking
#print axioms forest_nonnegative_source_variance_pos
#print axioms forest_nonnegative_source_variance
end ForestUnimodality
