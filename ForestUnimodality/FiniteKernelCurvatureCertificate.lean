import ForestUnimodality.FiniteKernelInterpolation
import ForestUnimodality.AnalyticNumericCertificate

/-! Executable rational witnesses for the genuine parameter curvature
bounds. Expressions are reconstructed from degree and damping, rather than
accepting a witness-supplied interpretation of the target. -/
namespace ForestUnimodality.FiniteKernelCurvatureCertificate

open AnalyticNumericCertificate BinomialParameterGaussian BinomialParameterDerivative

structure IntervalWitness where
  lo : ℚ
  hi : ℚ
  vmin : ℚ
  damping : ℚ
  deriving Repr

def IntervalWitness.check (w : IntervalWitness) : Bool := decide
  (0 ≤ w.lo ∧ w.lo ≤ w.hi ∧ w.hi ≤ 1 ∧ 0 < w.damping ∧ 0 ≤ w.vmin ∧
    w.vmin ≤ w.lo * (1 - w.lo) ∧ w.vmin ≤ w.hi * (1 - w.hi) ∧
    ((9 / 40 ≤ w.vmin ∧ w.damping ≤ w.vmin) ∨
      w.damping * piUpper ^ 2 ≤ 4 * w.vmin))

theorem IntervalWitness.endpoints (w : IntervalWitness) (hw : w.check = true) :
    (0 : ℝ) ≤ w.lo ∧ (w.lo : ℝ) ≤ w.hi ∧ (w.hi : ℝ) ≤ 1 := by
  have h := of_decide_eq_true hw
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.1⟩

theorem IntervalWitness.sound (w : IntervalWitness) (hw : w.check = true)
    {q : ℝ} (hq : q ∈ Set.Icc (w.lo : ℝ) (w.hi : ℝ)) :
    DampingValid q (w.damping : ℝ) := by
  have h : 0 ≤ w.lo ∧ w.lo ≤ w.hi ∧ w.hi ≤ 1 ∧ 0 < w.damping ∧ 0 ≤ w.vmin ∧
      w.vmin ≤ w.lo * (1 - w.lo) ∧ w.vmin ≤ w.hi * (1 - w.hi) ∧
      ((9 / 40 ≤ w.vmin ∧ w.damping ≤ w.vmin) ∨
        w.damping * piUpper ^ 2 ≤ 4 * w.vmin) := of_decide_eq_true hw
  rcases h with ⟨_, _, _, hc, hv, hva, hvb, hregime⟩
  have hc' : (0 : ℝ) < w.damping := by exact_mod_cast hc
  apply damping_of_interval (vmin := (w.vmin : ℝ)) hq.1 hq.2
    (by exact_mod_cast hva) (by exact_mod_cast hvb) hc'
  rcases hregime with hnear | hperiod
  · have hnQ : (9 : ℚ) ≤ w.vmin * 40 :=
      (div_le_iff₀ (by norm_num : (0 : ℚ) < 40)).mp hnear.1
    have hnR : (9 : ℝ) ≤ (w.vmin : ℝ) * 40 := by exact_mod_cast hnQ
    exact Or.inl ⟨by linarith, by exact_mod_cast hnear.2⟩
  · refine Or.inr ⟨by exact_mod_cast hv, ?_⟩
    have hp : Real.pi ≤ (piUpper : ℝ) := (Expr.check_sound .pi (by rfl)).2
    have hsq : Real.pi ^ 2 ≤ (piUpper : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
    have hcost : (w.damping : ℝ) * (piUpper : ℝ) ^ 2 ≤ 4 * (w.vmin : ℝ) := by
      exact_mod_cast hperiod
    exact (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
      ((mul_le_mul_of_nonneg_left hsq hc'.le).trans hcost)

def coarseCentral (n : ℕ) : ℚ := 6 * (n : ℚ) * (n - 1 : ℕ)
def coarseDirection (n : ℕ) : ℚ := 2 * ((n + 1 : ℕ) : ℚ) * n

def centralExpr (n : ℕ) (c lo hi : ℚ) : Expr :=
  .mul (.rat (coarseCentral n))
    (.inv (.mul (.rat (5 * (((n - 2 : ℕ) : ℚ) * c) ^ 2))
      (.sqrt (.rat (((n - 2 : ℕ) : ℚ) * c)) lo hi)))

def directionExpr (n : ℕ) (c lo hi : ℚ) : Expr :=
  .mul (.rat (coarseDirection n))
    (.inv (.mul (.rat (5 * (((n - 1 : ℕ) : ℚ) * c)))
      (.sqrt (.rat (((n - 1 : ℕ) : ℚ) * c)) lo hi)))

structure DegreeWitness where
  centralLo : ℚ
  centralHi : ℚ
  directionLo : ℚ
  directionHi : ℚ
  deriving Repr

def DegreeWitness.check (w : DegreeWitness) (n : ℕ) (c : ℚ) : Bool :=
  (if 2 < n then (centralExpr n c w.centralLo w.centralHi).check else true) &&
  (if 1 < n then (directionExpr n c w.directionLo w.directionHi).check else true)

def DegreeWitness.centralUpper (w : DegreeWitness) (n : ℕ) (c : ℚ) : ℚ :=
  if 2 < n then min (coarseCentral n) (centralExpr n c w.centralLo w.centralHi).upper
  else coarseCentral n

def DegreeWitness.directionUpper (w : DegreeWitness) (n : ℕ) (c : ℚ) : ℚ :=
  if 1 < n then min (coarseDirection n) (directionExpr n c w.directionLo w.directionHi).upper
  else coarseDirection n

theorem centralExpr_eval (n : ℕ) (c lo hi : ℚ) :
    (centralExpr n c lo hi).eval = 6 * (n : ℝ) * (n - 1 : ℕ) /
      (5 * (((n - 2 : ℕ) : ℝ) * (c : ℝ)) ^ 2 * Real.sqrt (((n - 2 : ℕ) : ℝ) * c)) := by
  simp only [centralExpr, coarseCentral, Expr.eval]
  push_cast
  ring

theorem directionExpr_eval (n : ℕ) (c lo hi : ℚ) :
    (directionExpr n c lo hi).eval = 2 * ((n + 1 : ℕ) : ℝ) * n /
      (5 * (((n - 1 : ℕ) : ℝ) * (c : ℝ)) * Real.sqrt (((n - 1 : ℕ) : ℝ) * c)) := by
  simp only [directionExpr, coarseDirection, Expr.eval]
  push_cast
  ring

theorem DegreeWitness.central_sound (w : DegreeWitness) (n : ℕ) (c : ℚ)
    (hw : w.check n c = true) (j : ℤ) {q : ℝ} (h : DampingValid q (c : ℝ)) :
    |centralSecond n j q| ≤ (w.centralUpper n c : ℝ) := by
  have hc : (if 2 < n then (centralExpr n c w.centralLo w.centralHi).check else true) = true :=
    (Bool.and_eq_true_iff.mp hw).1
  unfold DegreeWitness.centralUpper
  by_cases hn : 2 < n
  · rw [if_pos hn, Rat.cast_min]
    refine le_min ?_ ?_
    · simpa only [coarseCentral, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
        abs_centralSecond_le n j h.q_mem.1 h.q_mem.2
    · have he := (Expr.check_sound _ (by simpa only [if_pos hn] using hc)).2
      rw [centralExpr_eval] at he
      exact (abs_centralSecond_safe n hn j h).trans he
  · rw [if_neg hn]
    simpa only [coarseCentral, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      abs_centralSecond_le n j h.q_mem.1 h.q_mem.2

theorem DegreeWitness.left_sound (w : DegreeWitness) (n : ℕ) (c : ℚ)
    (hw : w.check n c = true) (j : ℤ) {q : ℝ} (h : DampingValid q (c : ℝ)) :
    |leftSecond n j q| ≤ (w.directionUpper n c : ℝ) := by
  have hc : (if 1 < n then (directionExpr n c w.directionLo w.directionHi).check else true) = true :=
    (Bool.and_eq_true_iff.mp hw).2
  unfold DegreeWitness.directionUpper
  by_cases hn : 1 < n
  · rw [if_pos hn, Rat.cast_min]
    refine le_min ?_ ?_
    · simpa only [coarseDirection, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
        abs_leftSecond_le n j h.q_mem.1 h.q_mem.2
    · have he := (Expr.check_sound _ (by simpa only [if_pos hn] using hc)).2
      rw [directionExpr_eval] at he
      exact (abs_leftSecond_safe n hn j h).trans he
  · rw [if_neg hn]
    simpa only [coarseDirection, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      abs_leftSecond_le n j h.q_mem.1 h.q_mem.2

theorem DegreeWitness.right_sound (w : DegreeWitness) (n : ℕ) (c : ℚ)
    (hw : w.check n c = true) (j : ℤ) {q : ℝ} (h : DampingValid q (c : ℝ)) :
    |rightSecond n j q| ≤ (w.directionUpper n c : ℝ) := by
  simpa only [rightSecond, abs_neg] using w.left_sound n c hw (j + 1) h

#print axioms centralExpr_eval
#print axioms IntervalWitness.sound
#print axioms directionExpr_eval
#print axioms DegreeWitness.central_sound
#print axioms DegreeWitness.left_sound
#print axioms DegreeWitness.right_sound

end ForestUnimodality.FiniteKernelCurvatureCertificate
