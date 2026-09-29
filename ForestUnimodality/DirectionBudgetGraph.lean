import ForestUnimodality.DirectionBudget

/-! From fixed analytic direction budgets to one actual graph law.
Source variance and tail estimates are explicit, shared-statistic inputs. -/
namespace ForestUnimodality.DirectionBudgetGraph
open Set DirectionBudget ReciprocalGradientBudget

variable {V : Type*} [DecidableEq V]

structure Inputs (p : Parameters) (G : SimpleGraph V) (S I : Finset V)
    (z m : ℝ) (k : ℕ) (g0 g1 : GradientProfile) : Prop where
  subset : I ⊆ S
  independent : G.IsIndepSet (I : Set V)
  activity_pos : 0 < z
  activity_mem : z ∈ Icc p.a p.b
  mean_available : m = hardCoreAvailableMean G S I z
  start_le : p.start ≤ m
  mean_rank : hardCoreMean G S z = (k : ℝ)
  variance_layer : hardCoreVariance G S z - (z / (1 + z)) * (1 - z / (1 + z)) * m ≤
    p.R * (((z / (1 + z)) * (1 - z / (1 + z))) * m)
  variance_available : hardCoreAvailableVariance G S I z ≤ p.D * m
  tail0 : hardCoreAvailableLowerTail G S I z (p.alpha * m) ≤ Real.exp (-p.rate0 * m)
  tail1 : hardCoreAvailableLowerTail G S I z (p.alpha1 * m) ≤ Real.exp (-p.rate1 * m)
  variance_min : p.vmin ≤ (z / (1 + z)) * (1 - z / (1 + z))
  variance_max : (z / (1 + z)) * (1 - z / (1 + z)) ≤ p.vmax
  asymmetry : |1 - 2 * (z / (1 + z))| ≤ p.eta
  cutoff : BernoulliCutoff.Valid (z / (1 + z)) p.T
  profile0 : g0.Valid (z / (1 + z)) p.vmin (p.alpha * m)
  profile1 : g1.Valid (z / (1 + z)) p.vmin (p.alpha1 * m)
  constant0 : g0.constant ≤ p.c0
  constant1 : g1.constant ≤ p.c1

variable {p : Parameters} {G : SimpleGraph V} {S I : Finset V}
  {z m : ℝ} {k : ℕ} {g0 g1 : GradientProfile}

theorem Inputs.mean_pos (h : Inputs p G S I z m k g0 g1) (hp : p.Valid) : 0 < m :=
  hp.start_pos.trans_le h.start_le

theorem Inputs.cutoff_count (h : Inputs p G S I z m k g0 g1) (hp : p.Valid) :
    1 < p.alpha * m :=
  hp.cutoff_count.trans_le (mul_le_mul_of_nonneg_left h.start_le hp.alpha_pos.le)

theorem actual_mass_lower (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (hbracket : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 p.start) :
    p.mass m ≤ Real.sqrt m *
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k := by
  have hb : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 m :=
    hbracket.trans (PointMassBudgetMonotonicity.mainBracket_monotoneOn
      hp.start_pos hp.D_nonneg hp.rate0_nonneg (by simp) h.start_le h.start_le)
  have he := PointMassLayerBudget.scaled_probability_lower_explicit G S I h.subset h.independent
    h.activity_pos h.mean_available (h.mean_pos hp) hp.alpha_pos hp.alpha_lt (h.cutoff_count hp)
    k h.mean_rank hp.R_nonneg hp.D_nonneg h.variance_layer h.variance_available h.tail0
    h.cutoff hp.vmin_pos h.variance_min h.asymmetry
  have hf := PointMassLayerBudget.weaken_prefactor
    (hp.vmin_pos.trans_le h.variance_min) h.variance_max hb he
  simpa only [Parameters.mass, Parameters.H, PointMassBudgetMonotonicity.budget,
    PointMassBudgetMonotonicity.mainBracket, PointMassBudgetMonotonicity.scaledError,
    PointMassBudgetMonotonicity.momentFactor, PointMassLayerBudget.errorBudget] using hf

theorem actual_gradient_bound (hp : p.Valid) (h : Inputs p G S I z m k g0 g1) (l : ℕ) :
    Real.sqrt m * |tiltedProbability (countIndependent G S) z (partitionFunction G S z) (l+1) -
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) l| ≤ p.gradient m := by
  have hm0 := h.mean_pos hp
  have hg0 (d : ℕ) (j : ℤ) (hd : p.alpha * m ≤ (d : ℝ)) :
      |gradient d j (z / (1 + z))| ≤ p.c0 / (p.vmin * d) := by
    exact (g0.gradient_bound h.profile0 d j hd).trans
      (div_le_div_of_nonneg_right h.constant0 (mul_nonneg hp.vmin_pos.le (Nat.cast_nonneg d)))
  have hg1 (d : ℕ) (j : ℤ) (hd : p.alpha1 * m ≤ (d : ℝ)) :
      |gradient d j (z / (1 + z))| ≤ p.c1 / (p.vmin * d) := by
    exact (g1.gradient_bound h.profile1 d j hd).trans
      (div_le_div_of_nonneg_right h.constant1 (mul_nonneg hp.vmin_pos.le (Nat.cast_nonneg d)))
  have hav : 0 < hardCoreAvailableMean G S I z := by rwa [← h.mean_available]
  have hprice : p.c1 / (p.vmin * p.alpha1) ≤ hardCoreAvailableMean G S I z := by
    rw [← h.mean_available]
    exact hp.price_lt_start.le.trans h.start_le
  have he := hardCore_gradient_bound G S I h.subset h.independent h.activity_pos l
    hp.alpha1_pos hp.alpha1_le hp.alpha_lt.le hav hp.vmin_pos hp.c0_nonneg hp.c1_nonneg
    hp.price_order hprice (by simpa only [← h.mean_available] using h.variance_available)
    (by simpa only [← h.mean_available] using h.tail0)
    (by simpa only [← h.mean_available] using h.tail1)
    (by simpa only [← h.mean_available] using hg0)
    (by simpa only [← h.mean_available] using hg1)
  simpa only [← h.mean_available, Parameters.gradient, Parameters.A0, Parameters.A1,
    GradientBudgetMonotonicity.gradientCost, GradientBudgetMonotonicity.shiftedCost, div_div] using he

theorem gradient_nonneg (hp : p.Valid) (h : Inputs p G S I z m k g0 g1) :
    0 ≤ p.gradient m :=
  (mul_nonneg (Real.sqrt_nonneg m) (abs_nonneg _)).trans (actual_gradient_bound hp h 0)

theorem actual_previous_gradient_bound (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (hk : 1 ≤ k) :
    Real.sqrt m * |tiltedProbability (countIndependent G S) z (partitionFunction G S z) (k-1) -
      tiltedProbability (countIndependent G S) z (partitionFunction G S z) k| ≤ p.gradient m := by
  have he := actual_gradient_bound hp h (k - 1)
  rw [Nat.sub_add_cancel hk, abs_sub_comm] at he
  exact he

theorem mass_nonneg_of_start (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (hmass : 0 ≤ p.mass p.start) : 0 ≤ p.mass m :=
  hmass.trans (hp.mass_monotoneOn (by simp) h.start_le h.start_le)

theorem actual_left_positive (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (hk : 1 ≤ k) (hb : p.b ≤ 1)
    (hbracket : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 p.start)
    (hmass : 0 ≤ p.mass p.start) (hmargin : 0 < p.leftMargin p.start) :
    0 < tiltedLeft (countIndependent G S) z (partitionFunction G S z) k := by
  have hbudget := hp.leftMargin_positive
    (h.activity_pos.le.trans h.activity_mem.2) hb hmargin h.start_le
  exact ProbabilityDirectionBudget.left_positive (countIndependent G S) k
    h.activity_pos (Real.sqrt_pos.mpr (h.mean_pos hp)) h.activity_mem.2 hb
    (mass_nonneg_of_start hp h hmass) (gradient_nonneg hp h)
    (actual_mass_lower hp h hbracket) (actual_previous_gradient_bound hp h hk) hbudget

theorem actual_right_positive (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (ha : 1 ≤ p.a)
    (hbracket : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 p.start)
    (hmass : 0 ≤ p.mass p.start) (hmargin : 0 < p.rightMargin p.start) :
    0 < tiltedRight (countIndependent G S) z (partitionFunction G S z) k := by
  have hbudget := hp.rightMargin_positive ha hmargin h.start_le
  exact ProbabilityDirectionBudget.right_positive (countIndependent G S) k
    h.activity_pos (Real.sqrt_pos.mpr (h.mean_pos hp)) h.activity_mem.1 ha
    (mass_nonneg_of_start hp h hmass) (actual_mass_lower hp h hbracket)
    (actual_gradient_bound hp h k) hbudget

theorem actual_left_coefficient_lt (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (hk : 1 ≤ k) (hb : p.b ≤ 1)
    (hbracket : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 p.start)
    (hmass : 0 ≤ p.mass p.start) (hmargin : 0 < p.leftMargin p.start) :
    countIndependent G S (k-1) < countIndependent G S k :=
  ProbabilityDirectionBudget.left_coefficient_lt (countIndependent G S)
    h.activity_pos (partitionFunction_pos G S h.activity_pos.le) hk
    (actual_left_positive hp h hk hb hbracket hmass hmargin)

theorem actual_right_coefficient_lt (hp : p.Valid) (h : Inputs p G S I z m k g0 g1)
    (ha : 1 ≤ p.a)
    (hbracket : 0 ≤ PointMassBudgetMonotonicity.mainBracket p.R p.D p.rate0 p.start)
    (hmass : 0 ≤ p.mass p.start) (hmargin : 0 < p.rightMargin p.start) :
    countIndependent G S (k+1) < countIndependent G S k :=
  ProbabilityDirectionBudget.right_coefficient_lt (countIndependent G S)
    h.activity_pos (partitionFunction_pos G S h.activity_pos.le) k
    (actual_right_positive hp h ha hbracket hmass hmargin)

#print axioms actual_mass_lower
#print axioms actual_gradient_bound
#print axioms actual_left_coefficient_lt
#print axioms actual_right_coefficient_lt
end ForestUnimodality.DirectionBudgetGraph
