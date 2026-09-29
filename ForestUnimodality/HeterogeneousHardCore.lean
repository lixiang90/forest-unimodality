import ForestUnimodality.HardCoreMoments
import ForestUnimodality.GraphRecursion
import ForestUnimodality.KernelBudget
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Genuine heterogeneous hard-core weights, their deletion recursion and
exponential tilts by a fixed signed mark. Derivatives and Cauchy--Schwarz are
proved first for finite weighted spaces, then instantiated on independent
subsets. No common-activity variance formula or forest source bound is assumed. -/

namespace ForestUnimodality.FiniteTilt

open Finset

noncomputable def total {α : Type*} (s : Finset α) (w : α → ℝ) : ℝ := ∑ x ∈ s, w x
noncomputable def numerator {α : Type*} (s : Finset α) (w b : α → ℝ) : ℝ := ∑ x ∈ s, w x * b x
noncomputable def mean {α : Type*} (s : Finset α) (w b : α → ℝ) : ℝ := numerator s w b / total s w
noncomputable def covariance {α : Type*} (s : Finset α) (w b a : α → ℝ) : ℝ :=
  mean s w (fun x => b x * a x) - mean s w b * mean s w a
noncomputable def variance {α : Type*} (s : Finset α) (w b : α → ℝ) : ℝ := covariance s w b b
noncomputable def tilt {α : Type*} (w a : α → ℝ) (t : ℝ) (x : α) : ℝ := w x * Real.exp (t * a x)

theorem hasDerivAt_numerator {α : Type*} (s : Finset α) (w a b : α → ℝ) (t : ℝ) :
    HasDerivAt (fun u => numerator s (tilt w a u) b)
      (numerator s (tilt w a t) (fun x => b x * a x)) t := by
  have hd := HasDerivAt.fun_sum (u := s) (fun x _ =>
    ((((hasDerivAt_id t).mul_const (a x)).exp.const_mul (w x)).mul_const (b x)))
  apply hd.congr_deriv
  apply sum_congr rfl
  intro x _
  simp only [tilt, id_eq, one_mul]
  ring

theorem hasDerivAt_total {α : Type*} (s : Finset α) (w a : α → ℝ) (t : ℝ) :
    HasDerivAt (fun u => total s (tilt w a u)) (numerator s (tilt w a t) a) t := by
  simpa only [numerator, total, mul_one, one_mul] using
    hasDerivAt_numerator s w a (fun _ => 1) t

theorem hasDerivAt_mean {α : Type*} (s : Finset α) (w a b : α → ℝ) (t : ℝ)
    (hZ : total s (tilt w a t) ≠ 0) :
    HasDerivAt (fun u => mean s (tilt w a u) b) (covariance s (tilt w a t) b a) t := by
  apply ((hasDerivAt_numerator s w a b t).div (hasDerivAt_total s w a t) hZ).congr_deriv
  unfold covariance mean
  field_simp

theorem covariance_centered {α : Type*} (s : Finset α) (w b a : α → ℝ)
    (hZ : total s w ≠ 0) :
    covariance s w b a = mean s w (fun x => (b x - mean s w b) * (a x - mean s w a)) := by
  have hs : numerator s w (fun x => (b x - mean s w b) * (a x - mean s w a)) =
      numerator s w (fun x => b x * a x) - mean s w a * numerator s w b -
        mean s w b * numerator s w a + mean s w b * mean s w a * total s w := by
    have hp (x : α) : w x * ((b x - mean s w b) * (a x - mean s w a)) =
        w x * (b x * a x) - mean s w a * (w x * b x) -
          mean s w b * (w x * a x) + mean s w b * mean s w a * w x := by ring
    simp only [numerator, total, hp, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  unfold mean at hs ⊢
  rw [hs]
  unfold covariance mean
  field_simp
  ring

theorem variance_centered {α : Type*} (s : Finset α) (w b : α → ℝ)
    (hZ : total s w ≠ 0) :
    variance s w b = mean s w (fun x => (b x - mean s w b) ^ 2) := by
  simpa only [variance, pow_two] using covariance_centered s w b b hZ

theorem weighted_cauchy {α : Type*} (s : Finset α) (w b a : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    numerator s w (fun x => b x * a x) ^ 2 ≤
      numerator s w (fun x => b x ^ 2) * numerator s w (fun x => a x ^ 2) := by
  have hc := sum_mul_sq_le_sq_mul_sq s (fun x => Real.sqrt (w x) * b x)
    (fun x => Real.sqrt (w x) * a x)
  have hcross : (∑ x ∈ s, (Real.sqrt (w x) * b x) * (Real.sqrt (w x) * a x)) =
      numerator s w (fun x => b x * a x) := by
    apply sum_congr rfl
    intro x hx
    calc
      _ = Real.sqrt (w x) ^ 2 * (b x * a x) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw x hx)]
  have hsq (f : α → ℝ) : (∑ x ∈ s, (Real.sqrt (w x) * f x) ^ 2) =
      numerator s w (fun x => f x ^ 2) := by
    apply sum_congr rfl
    intro x hx
    rw [mul_pow, Real.sq_sqrt (hw x hx)]
  rwa [hcross, hsq b, hsq a] at hc

theorem covariance_sq_le_variance_mul_variance {α : Type*}
    (s : Finset α) (w b a : α → ℝ) (hw : ∀ x ∈ s, 0 ≤ w x) (hZ : 0 < total s w) :
    covariance s w b a ^ 2 ≤ variance s w b * variance s w a := by
  rw [covariance_centered s w b a (ne_of_gt hZ), variance_centered s w b (ne_of_gt hZ),
    variance_centered s w a (ne_of_gt hZ)]
  simp only [mean, div_pow, div_mul_div_comm]
  have hc := weighted_cauchy s w (fun x => b x - mean s w b) (fun x => a x - mean s w a) hw
  simpa only [mean, pow_two] using div_le_div_of_nonneg_right hc (sq_nonneg (total s w))

end ForestUnimodality.FiniteTilt

namespace ForestUnimodality

open Finset
variable {V : Type*} [DecidableEq V]

noncomputable def heterogeneousWeight (activity : V → ℝ) (J : Finset V) : ℝ := ∏ v ∈ J, activity v
noncomputable def heterogeneousPartition (G : SimpleGraph V) (S : Finset V) (activity : V → ℝ) : ℝ :=
  ∑ J ∈ independentSubsets G S, heterogeneousWeight activity J
noncomputable def heterogeneousMean (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (b : Finset V → ℝ) : ℝ :=
  FiniteTilt.mean (independentSubsets G S) (heterogeneousWeight activity) b
noncomputable def heterogeneousCovariance (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (b a : Finset V → ℝ) : ℝ :=
  FiniteTilt.covariance (independentSubsets G S) (heterogeneousWeight activity) b a
noncomputable def heterogeneousVariance (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (b : Finset V → ℝ) : ℝ :=
  FiniteTilt.variance (independentSubsets G S) (heterogeneousWeight activity) b
noncomputable def heterogeneousMarginal (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (v : V) : ℝ := heterogeneousMean G S activity (fun J => if v ∈ J then 1 else 0)

omit [DecidableEq V] in
theorem heterogeneousWeight_nonneg {activity : V → ℝ} {J : Finset V}
    (h : ∀ v ∈ J, 0 ≤ activity v) : 0 ≤ heterogeneousWeight activity J := prod_nonneg h

theorem one_le_heterogeneousPartition (G : SimpleGraph V) (S : Finset V) (activity : V → ℝ)
    (hactivity : ∀ v ∈ S, 0 ≤ activity v) : 1 ≤ heterogeneousPartition G S activity := by
  have h := single_le_sum (s := independentSubsets G S) (f := heterogeneousWeight activity)
    (fun J hJ => heterogeneousWeight_nonneg (fun v hv => hactivity v ((mem_independentSubsets.mp hJ).1 hv)))
    (empty_mem_independentSubsets G S)
  simpa only [heterogeneousWeight, prod_empty, heterogeneousPartition] using h

theorem heterogeneousPartition_pos (G : SimpleGraph V) (S : Finset V) (activity : V → ℝ)
    (hactivity : ∀ v ∈ S, 0 ≤ activity v) : 0 < heterogeneousPartition G S activity :=
  zero_lt_one.trans_le (one_le_heterogeneousPartition G S activity hactivity)

theorem heterogeneousPartition_delete_vertex (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v : V} (hv : v ∈ S) :
    heterogeneousPartition G S activity = heterogeneousPartition G (S.erase v) activity +
      activity v * heterogeneousPartition G (S \ closedNeighborhoodIn G S v) activity := by
  classical
  unfold heterogeneousPartition
  rw [sum_independentSubsets_delete_vertex G S hv, mul_sum]
  congr 1
  apply sum_congr rfl
  intro J hJ
  exact prod_insert (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ)

theorem heterogeneousNumerator_delete_vertex (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (b : Finset V → ℝ) {v : V} (hv : v ∈ S) :
    FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity) b =
      FiniteTilt.numerator (independentSubsets G (S.erase v)) (heterogeneousWeight activity) b +
        activity v * FiniteTilt.numerator (independentSubsets G (S \ closedNeighborhoodIn G S v))
          (heterogeneousWeight activity) (fun J => b (insert v J)) := by
  classical
  unfold FiniteTilt.numerator
  rw [sum_independentSubsets_delete_vertex G S hv, mul_sum]
  congr 1
  apply sum_congr rfl
  intro J hJ
  rw [heterogeneousWeight, prod_insert (not_mem_of_independentSubsets_sdiff_closedNeighborhoodIn hJ)]
  simp only [heterogeneousWeight, mul_assoc]

noncomputable def markedSum (a : V → ℝ) (J : Finset V) : ℝ := ∑ v ∈ J, a v
noncomputable def tiltedActivities (activity a : V → ℝ) (t : ℝ) (v : V) : ℝ :=
  activity v * Real.exp (t * a v)

omit [DecidableEq V] in
theorem heterogeneousWeight_tilt (activity a : V → ℝ) (t : ℝ) (J : Finset V) :
    heterogeneousWeight (tiltedActivities activity a t) J =
      FiniteTilt.tilt (heterogeneousWeight activity) (markedSum a) t J := by
  simp only [heterogeneousWeight, tiltedActivities, prod_mul_distrib, ← Real.exp_sum,
    ← mul_sum, FiniteTilt.tilt, markedSum]

omit [DecidableEq V] in
theorem tiltedActivities_nonneg (activity a : V → ℝ) {S : Finset V}
    (hactivity : ∀ v ∈ S, 0 ≤ activity v) (t : ℝ) :
    ∀ v ∈ S, 0 ≤ tiltedActivities activity a t v := by
  intro v hv
  exact mul_nonneg (hactivity v hv) (Real.exp_pos _).le

theorem hasDerivAt_heterogeneousPartition_tilt (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => heterogeneousPartition G S (tiltedActivities activity a u))
      (FiniteTilt.numerator (independentSubsets G S)
        (heterogeneousWeight (tiltedActivities activity a t)) (markedSum a)) t := by
  simpa only [heterogeneousPartition, FiniteTilt.total, FiniteTilt.numerator, heterogeneousWeight_tilt] using
    FiniteTilt.hasDerivAt_total (independentSubsets G S) (heterogeneousWeight activity) (markedSum a) t

theorem hasDerivAt_heterogeneousMean_tilt (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) (hactivity : ∀ v ∈ S, 0 ≤ activity v)
    (b : Finset V → ℝ) (t : ℝ) :
    HasDerivAt (fun u => heterogeneousMean G S (tiltedActivities activity a u) b)
      (heterogeneousCovariance G S (tiltedActivities activity a t) b (markedSum a)) t := by
  have hZ := heterogeneousPartition_pos G S (tiltedActivities activity a t)
    (tiltedActivities_nonneg activity a hactivity t)
  have hf : ∀ u, heterogeneousWeight (tiltedActivities activity a u) =
      FiniteTilt.tilt (heterogeneousWeight activity) (markedSum a) u := by
    intro u
    funext J
    exact heterogeneousWeight_tilt activity a u J
  have hZ' : FiniteTilt.total (independentSubsets G S)
      (FiniteTilt.tilt (heterogeneousWeight activity) (markedSum a) t) ≠ 0 := by
    rw [← hf t]
    exact ne_of_gt hZ
  simpa only [heterogeneousMean, heterogeneousCovariance, hf] using
    FiniteTilt.hasDerivAt_mean (independentSubsets G S) (heterogeneousWeight activity) (markedSum a) b t hZ'

theorem hasDerivAt_markedMean_tilt (G : SimpleGraph V) (S : Finset V)
    (activity a : V → ℝ) (hactivity : ∀ v ∈ S, 0 ≤ activity v) (t : ℝ) :
    HasDerivAt (fun u => heterogeneousMean G S (tiltedActivities activity a u) (markedSum a))
      (heterogeneousVariance G S (tiltedActivities activity a t) (markedSum a)) t :=
  hasDerivAt_heterogeneousMean_tilt G S activity a hactivity (markedSum a) t

theorem heterogeneousCovariance_sq_le (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (hactivity : ∀ v ∈ S, 0 ≤ activity v) (b a : Finset V → ℝ) :
    heterogeneousCovariance G S activity b a ^ 2 ≤
      heterogeneousVariance G S activity b * heterogeneousVariance G S activity a := by
  apply FiniteTilt.covariance_sq_le_variance_mul_variance
  · intro J hJ
    exact heterogeneousWeight_nonneg (fun v hv => hactivity v ((mem_independentSubsets.mp hJ).1 hv))
  · exact heterogeneousPartition_pos G S activity hactivity

theorem heterogeneousMarginal_eq_delete_ratio (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) {v : V} (hv : v ∈ S) :
    heterogeneousMarginal G S activity v =
      activity v * heterogeneousPartition G (S \ closedNeighborhoodIn G S v) activity /
        heterogeneousPartition G S activity := by
  classical
  have hnum := heterogeneousNumerator_delete_vertex G S activity
    (fun J => if v ∈ J then 1 else 0) hv
  have hzero : FiniteTilt.numerator (independentSubsets G (S.erase v))
      (heterogeneousWeight activity) (fun J => if v ∈ J then 1 else 0) = 0 := by
    apply sum_eq_zero
    intro J hJ
    have hn : v ∉ J := fun hvJ => (mem_erase.mp ((mem_independentSubsets.mp hJ).1 hvJ)).1 rfl
    simp [hn]
  have hone : FiniteTilt.numerator (independentSubsets G (S \ closedNeighborhoodIn G S v))
      (heterogeneousWeight activity) (fun J => if v ∈ insert v J then 1 else 0) =
      heterogeneousPartition G (S \ closedNeighborhoodIn G S v) activity := by
    simp [FiniteTilt.numerator, heterogeneousPartition]
  rw [hzero, hone, zero_add] at hnum
  unfold heterogeneousMarginal heterogeneousMean FiniteTilt.mean
  rw [hnum]
  rfl

theorem heterogeneousMarginal_mem_Icc (G : SimpleGraph V) (S : Finset V)
    (activity : V → ℝ) (hactivity : ∀ v ∈ S, 0 ≤ activity v) (v : V) :
    heterogeneousMarginal G S activity v ∈ Set.Icc 0 1 := by
  classical
  have hZ := heterogeneousPartition_pos G S activity hactivity
  have hw (J) (hJ : J ∈ independentSubsets G S) : 0 ≤ heterogeneousWeight activity J :=
    heterogeneousWeight_nonneg (fun w hw => hactivity w ((mem_independentSubsets.mp hJ).1 hw))
  have hn : 0 ≤ FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity)
      (fun J => if v ∈ J then 1 else 0) := by
    apply sum_nonneg
    intro J hJ
    dsimp only
    split_ifs <;> simp only [mul_one, mul_zero] <;> first | exact hw J hJ | exact le_rfl
  have hl : FiniteTilt.numerator (independentSubsets G S) (heterogeneousWeight activity)
      (fun J => if v ∈ J then 1 else 0) ≤ heterogeneousPartition G S activity := by
    apply sum_le_sum
    intro J hJ
    dsimp only
    split_ifs <;> simp only [mul_one, mul_zero] <;> first | exact le_rfl | exact hw J hJ
  exact ⟨div_nonneg hn hZ.le, (div_le_one hZ).mpr hl⟩

/-- The independent-set splitting bijection transports arbitrary weights. -/
theorem sum_independentSubsets_by_split {R : Type*} [AddCommMonoid R]
    (G : SimpleGraph V) (S I : Finset V) (hIS : I ⊆ S)
    (hI : G.IsIndepSet (I : Set V)) (F : Finset V → R) :
    (∑ K ∈ independentSubsets G S, F K) =
      ∑ J ∈ independentSubsets G (S \ I), ∑ T ∈ (available G I J).powerset, F (J ∪ T) := by
  classical
  rw [sum_sigma']
  apply sum_bij' (fun K _ => (⟨K \ I, K ∩ I⟩ : (J : Finset V) × Finset V))
    (fun p _ => p.1 ∪ p.2)
  · intro K hK
    exact mem_sigma.mpr ⟨split_left_mem hK, mem_powerset.mpr (split_right_subset hK)⟩
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    exact join_mem hIS hI hJ (mem_powerset.mp hT)
  · intro K _
    exact split_union K I
  · intro p hp
    obtain ⟨hJ, hT⟩ := mem_sigma.mp hp
    exact Sigma.ext (join_sdiff hJ (mem_powerset.mp hT))
      (heq_of_eq (join_inter hJ (mem_powerset.mp hT)))
  · intro K _
    rw [split_union]

noncomputable def independentTiltActivities (I : Finset V) (z t : ℝ) (v : V) : ℝ :=
  if v ∈ I then t * z else z

theorem heterogeneousPartition_independent_tilt_layers (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) (z t : ℝ) :
    heterogeneousPartition G S (independentTiltActivities I z t) =
      ∑ j ∈ range ((S \ I).card + 1), ∑ m ∈ range (I.card + 1),
        (layerCount G I (S \ I) j m : ℝ) * z ^ j * (1 + t * z) ^ m := by
  classical
  unfold heterogeneousPartition
  rw [sum_independentSubsets_by_split G S I hIS hI]
  have hsplit : (∑ J ∈ independentSubsets G (S \ I),
      ∑ T ∈ (available G I J).powerset,
        heterogeneousWeight (independentTiltActivities I z t) (J ∪ T)) =
      ∑ J ∈ independentSubsets G (S \ I), z ^ J.card * (1 + t * z) ^ (available G I J).card := by
    apply sum_congr rfl
    intro J hJ
    have hJS := (mem_independentSubsets.mp hJ).1
    have hweight : ∀ T ∈ (available G I J).powerset,
        heterogeneousWeight (independentTiltActivities I z t) (J ∪ T) = z ^ J.card * (t * z) ^ T.card := by
      intro T hT
      have hTI : T ⊆ I := (mem_powerset.mp hT).trans (available_subset _ _ _)
      have hdis : Disjoint J T := disjoint_left.mpr (fun v hvJ hvT =>
        (mem_sdiff.mp (hJS hvJ)).2 (hTI hvT))
      unfold heterogeneousWeight
      rw [prod_union hdis]
      have hjprod : (∏ v ∈ J, independentTiltActivities I z t v) = z ^ J.card := by
        calc
          _ = ∏ _v ∈ J, z := by
            apply prod_congr rfl
            intro v hv
            simp only [independentTiltActivities, if_neg (mem_sdiff.mp (hJS hv)).2]
          _ = _ := by simp
      have htprod : (∏ v ∈ T, independentTiltActivities I z t v) = (t * z) ^ T.card := by
        calc
          _ = ∏ _v ∈ T, t * z := by
            apply prod_congr rfl
            intro v hv
            simp only [independentTiltActivities, if_pos (hTI hv)]
          _ = _ := by simp
      rw [hjprod, htprod]
    rw [sum_congr rfl hweight, ← mul_sum, sum_powerset_pow_card]
  rw [hsplit, sum_independentSubsets_by_layers G I (S \ I) (fun j m => z ^ j * (1 + t * z) ^ m)]
  simp only [mul_assoc]

/-- The fixed-I Laplace transform is exactly a heterogeneous partition
ratio. The algebraic identity allows every real t, so in particular includes
the zero-activity boundary t=0 used by nonnegative tilts. -/
theorem hardCoreLayerLaplace_eq_heterogeneous_ratio (G : SimpleGraph V) (S I : Finset V)
    (hIS : I ⊆ S) (hI : G.IsIndepSet (I : Set V)) {z : ℝ} (hz : 0 < z) (t : ℝ) :
    hardCoreLayerLaplace G S I z t =
      heterogeneousPartition G S (independentTiltActivities I z t) / partitionFunction G S z := by
  rw [heterogeneousPartition_independent_tilt_layers G S I hIS hI]
  simp only [hardCoreLayerLaplace, hardCoreLayerExpectation, sum_div]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro m _
  have hne : 1 + z ≠ 0 := by positivity
  have ha : (1 + z) * (1 - z / (1 + z) + z / (1 + z) * t) = 1 + t * z := by
    field_simp
    ring
  have hp : (1 + z) ^ m * (1 - z / (1 + z) + z / (1 + z) * t) ^ m = (1 + t * z) ^ m := by
    rw [← mul_pow, ha]
  unfold hardCoreLayerWeight
  calc
    _ = (layerCount G I (S \ I) j m : ℝ) * z ^ j *
      ((1 + z) ^ m * (1 - z / (1 + z) + z / (1 + z) * t) ^ m) / partitionFunction G S z := by ring
    _ = _ := by rw [hp]

#print axioms FiniteTilt.covariance_sq_le_variance_mul_variance
#print axioms heterogeneousPartition_delete_vertex
#print axioms hasDerivAt_heterogeneousMean_tilt
#print axioms hasDerivAt_markedMean_tilt
#print axioms heterogeneousCovariance_sq_le
#print axioms heterogeneousMarginal_eq_delete_ratio
#print axioms hardCoreLayerLaplace_eq_heterogeneous_ratio

end ForestUnimodality
