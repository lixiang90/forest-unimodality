import ForestUnimodality.AffineSourceCells

namespace ForestUnimodality.AffineSource
open BernsteinCertificate ParametricQuadratic

def leafBounds (P : Parameters) (D : Domain) : Bounds :=
  ⟨P.A/probabilityCap D,0,0,1-probabilityCap D/2,1-probabilityCap D⟩

def leafLower (D : Domain) : ℚ := 1/(1+D.b*(1-probabilityCap D))

def leafCheck (P : Parameters) (D : Domain) (c : Certificate) : Bool :=
  intervalCheck (positiveQuad P (leafBounds P D)).C (leafLower D) 1 c

theorem leafCheck_sound {P : Parameters} {D : Domain} {c : Certificate}
    (hc : leafCheck P D c=true) (hD : D.Valid) (hP : P.check=true) {r : ℝ}
    (hr : 1/(1+(D.b:ℝ)*(1-(probabilityCap D:ℝ)))≤r) (hr1 : r≤1) :
    0≤affineSourceRow P.toReal D.b (probabilityCap D) r 1 1 := by
  let q : ℝ := probabilityCap D
  have hb1 : 0<1+(D.b:ℝ) := by linarith [hD.b_pos]
  have hqeq : q=(D.b:ℝ)/(1+(D.b:ℝ)) := by simp [q,probabilityCap]
  have hq : 0<q := by rw [hqeq]; exact div_pos hD.b_pos hb1
  have hq1 : q<1 := by rw [hqeq]; exact (div_lt_one hb1).mpr (by linarith)
  have hden : 0<1+(D.b:ℝ)*(1-q) := by nlinarith [mul_pos hD.b_pos (sub_pos.mpr hq1)]
  have hr0 : 0≤r := (div_nonneg (by norm_num) hden.le).trans hr
  have hrlo : (leafLower D:ℝ)≤r := by
    simpa only [leafLower,Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_mul,Rat.cast_sub] using hr
  have hpoly := intervalCheck_sound hc (x:=r) ⟨hrlo,by simpa using hr1⟩
  have he := positiveQuad_identity P (leafBounds P D) r 0 (by norm_num)
  simp only [add_zero,Quad.value,zero_pow (by decide : 2≠0),mul_zero,zero_add] at he
  have hen : 0≤envelope P (leafBounds P D) r 1 := by rw [he]; exact hpoly
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
  apply hen.trans
  apply envelope_le P (leafBounds P D) hP hD.b_pos hq hr0 hr1
  · simp only [leafBounds,Rat.cast_div]
    exact le_rfl
  · simpa only [leafBounds,Rat.cast_zero] using hcap
  · simp only [leafBounds,Rat.cast_sub,Rat.cast_one,Rat.cast_div,Rat.cast_ofNat]
    exact le_rfl
  · simp only [leafBounds,Rat.cast_sub,Rat.cast_one]
    exact le_rfl

/-- Exact interval coverage includes every positive probability, including
the arbitrarily small origin limit; the actual leaf response is separate. -/
theorem sourceRowValid_of_checked (P : Parameters) (D : Domain) (leaf : Certificate) (cells : List Cell)
    (hP : P.check=true) (hD : D.check=true) (hleaf : leafCheck P D leaf=true)
    (hcells : cells.all (fun c=>c.check P D)=true)
    (hcover : SourceIntervalCoverage.check Cell.left Cell.right 0 (probabilityCap D) cells=true) :
    AffineSourceRowValid P.toReal D.b := by
  intro p r z hp hpq hr hr1 hend
  have hD' := Domain.check_sound hD
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
end ForestUnimodality.AffineSource
