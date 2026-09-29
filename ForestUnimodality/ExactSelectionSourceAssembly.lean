import ForestUnimodality.ExactSelectionSourceCells

namespace ForestUnimodality.ExactSelectionSource
open SelectionSource BernsteinCertificate ParametricQuadratic

def leafBounds (D : Domain) (hh : ℚ) : Bounds :=
  ⟨0,0,hh,1-probabilityCap D,0,
    affineSlope (probabilityCap D) (probabilityCap D) true,
    affineIntercept (probabilityCap D) true⟩

def leafLower (D : Domain) : ℚ := 1/(1+D.b*(1-probabilityCap D))

def leafCheck (P : Parameters) (D : Domain) (hh : ℚ)
    (log : SourceLogWitness) (c : Certificate) : Bool :=
  exactHCheck (probabilityCap D) hh log &&
    intervalCheck (positiveQuad P (leafBounds D hh)).C (leafLower D) 1 c

theorem leafCheck_sound {P : Parameters} {D : Domain} {hh : ℚ}
    {log : SourceLogWitness} {c : Certificate}
    (hc : leafCheck P D hh log c=true) (hD : D.Valid) (hP : P.check=true)
    {r parentp : ℝ}
    (hr : 1/(1+(D.b:ℝ)*(1-(probabilityCap D:ℝ)))≤r) (hr1 : r≤1) :
    0≤messageSourceScalarRow (toMessage P) D.lower D.b (probabilityCap D) r 1 parentp := by
  have hchecks := Bool.and_eq_true_iff.mp hc
  let q : ℝ := probabilityCap D
  have hb1 : 0<1+(D.b:ℝ) := by linarith [hD.b_pos]
  have hqeq : q=(D.b:ℝ)/(1+(D.b:ℝ)) := by simp [q,probabilityCap]
  have hq1 : q<1 := by rw [hqeq]; exact (div_lt_one hb1).mpr (by linarith)
  have hden : 0<1+(D.b:ℝ)*(1-q) := by nlinarith [mul_pos hD.b_pos (sub_pos.mpr hq1)]
  have hr0 : 0≤r := (div_nonneg (by norm_num) hden.le).trans hr
  have hrlo : (leafLower D:ℝ)≤r := by
    simpa only [leafLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub] using hr
  have hpoly := intervalCheck_sound hchecks.2 (x:=r) ⟨hrlo,by simpa using hr1⟩
  have he := positiveQuad_identity P (leafBounds D hh) r 0 (by norm_num)
  simp only [add_zero,Quad.value,zero_pow (by decide : 2≠0),mul_zero,zero_add] at he
  have hen : 0≤envelope P (leafBounds D hh) r 1 := by rw [he]; exact hpoly
  have hT : sourceLogCapacity D.b q=0 := by
    unfold sourceLogCapacity
    have hratio : (D.b:ℝ)*(1-q)/q=1 := by
      rw [hqeq]
      field_simp [hD.b_pos.ne',hb1.ne']
      ring
    rw [hratio,Real.log_one]
  have hcap : (0:ℝ)≤1/(q*sourceLogCapacity D.b q) ∧
      (0:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b q) := by
    simp [hT,sourceOddsCapacity]
  have hphi : 0≤sourcePhi D.lower D.b q := by
    unfold sourcePhi
    apply mul_nonneg
    · exact div_nonneg (div_nonneg hD.b_pos.le hb1.le) (Real.log_pos (by linarith [hD.b_pos])).le
    · exact le_max_left _ _
  apply hen.trans
  apply ExactSelectionSource.envelope_le P (leafBounds D hh) hP hr0 hr1
  · simp [leafBounds]
  · simp [leafBounds]
  · simpa only [leafBounds,Rat.cast_zero] using hcap
  · simpa only [leafBounds,Rat.cast_zero] using hphi
  · exact exactHCheck_sound hchecks.1
  · simp only [leafBounds,Rat.cast_sub,Rat.cast_one]
    exact le_rfl
  · exact affine_lower D hD.b_pos (probabilityCap D) true (le_refl _) hr0

/-- Exact logarithmic capacity, all real responses and retention values,
the entire positive probability domain, and its leaf endpoint. -/
theorem sourceRowValid_of_checked (P : Parameters) (D : Domain)
    (hh : ℚ) (log : SourceLogWitness) (leaf : Certificate) (cells : List Cell)
    (hP : P.check=true) (hD : D.check=true)
    (hleaf : leafCheck P D hh log leaf=true)
    (hcells : cells.all (fun c=>c.check P D)=true)
    (hcover : SourceIntervalCoverage.check Cell.left Cell.right 0 (probabilityCap D) cells=true) :
    MessageSourceRowValid (toMessage P) D.lower D.b := by
  intro p r z parentp hp hpq hr hr1 _ _ hend
  have hD' := ParametricSource.Domain.check_sound hD
  have hq : (probabilityCap D:ℝ)=(D.b:ℝ)/(1+(D.b:ℝ)) := by simp [probabilityCap]
  by_cases he : p=(probabilityCap D:ℝ)
  · have hz := hend (he.trans hq)
    subst p
    subst z
    exact leafCheck_sound hleaf hD' hP hr hr1
  · have hpq' : p<(D.b:ℝ)/(1+(D.b:ℝ)) := lt_of_le_of_ne hpq (fun hh=>he (hh.trans hq.symm))
    obtain ⟨cell,hmem,hlo,hhi⟩ := SourceIntervalCoverage.check_sound Cell.left Cell.right hcover
      (p:=p) (by simpa only [Rat.cast_zero] using hp) (hq.symm ▸ hpq)
    exact Cell.check_sound ((List.all_eq_true.mp hcells) cell hmem) hD' hP hp hlo hhi hpq' hr hr1

#print axioms leafCheck_sound
#print axioms sourceRowValid_of_checked
end ForestUnimodality.ExactSelectionSource
