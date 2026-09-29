import ForestUnimodality.Stage350SourceAllOrders
import ForestUnimodality.AffineSourceLaplaceRate

/-! Quantified source-window semantics, independent of order thresholds.
Every scalar acceptance obligation is rational. Forest density, variance,
and fixed-set Laplace estimates are consequences of proved source libraries. -/
namespace ForestUnimodality.FiniteSourceWindow
open Stage350SourceTable

structure Window where
  parent : Fin 43
  qa : ℚ
  qb : ℚ
  rho : ℚ
  D : ℚ
  R : ℚ
  vmax : ℚ
  source : Sum (Fin 15) (Fin 10)
  deriving Repr

def Window.lower (w : Window) : ℚ := w.qa/(1-w.qa)
def Window.upper (w : Window) : ℚ := w.qb/(1-w.qb)
def Window.CW (w : Window) : ℚ := (row w.parent).CW

def Window.varianceCheck (w : Window) : Prop :=
  match w.source with
  | .inl j => w.upper≤(AffineSourceLibrary.domain j).b ∧
    (let A := (AffineSourceLibrary.parameters j).A
     let C := (AffineSourceLibrary.parameters j).C
     let B := 2*A/w.rho+C-1
     (B*w.qb≤2*A ∧ 1+B/w.qb-A/w.qb^2≤w.D) ∨
     (2*A≤B*w.qa ∧ 1+B/w.qa-A/w.qa^2≤w.D))
  | .inr j => (Stage350SourceBudget.markedRow j).lower≤w.lower ∧
    w.upper≤(Stage350SourceBudget.markedRow j).upper ∧
    1+((Stage350SourceBudget.markedRow j).factor-1)/w.qa≤w.D
instance (w : Window) : Decidable w.varianceCheck := by
  unfold Window.varianceCheck
  split <;> infer_instance

structure Window.Valid (w : Window) : Prop where
  qa_pos : 0<w.qa
  qa_le_qb : w.qa≤w.qb
  qb_lt_one : w.qb<1
  rho_pos : 0<w.rho
  parent_lower : (row w.parent).a≤w.lower
  parent_upper : w.upper≤(row w.parent).b
  density : if 1≤w.lower then (1+w.lower)*w.rho^2≤2*w.lower*(276393/1000000)^2
    else w.rho≤max (1/4) (276393/1000000-max (nonnegative w.parent).A (43/100)*(1-w.lower)/w.lower)
  R_nonneg : 0≤w.R
  R_bound : w.CW/(1-w.qb)-1≤w.R
  variance_bound : w.varianceCheck
  variance_cap : (w.qb≤1/2 ∧ w.qb*(1-w.qb)≤w.vmax) ∨
    (1/2≤w.qa ∧ w.qa*(1-w.qa)≤w.vmax) ∨ 1/4≤w.vmax

instance (w : Window) : Decidable w.Valid :=
  decidable_of_iff ((0<w.qa) ∧
    (w.qa≤w.qb) ∧
    (w.qb<1) ∧
    (0<w.rho) ∧
    ((row w.parent).a≤w.lower) ∧
    (w.upper≤(row w.parent).b) ∧
    (if 1≤w.lower then (1+w.lower)*w.rho^2≤2*w.lower*(276393/1000000)^2 else w.rho≤max (1/4) (276393/1000000-max (nonnegative w.parent).A (43/100)*(1-w.lower)/w.lower)) ∧
    (0≤w.R) ∧
    (w.CW/(1-w.qb)-1≤w.R) ∧
    (w.varianceCheck) ∧
    ((w.qb≤1/2 ∧ w.qb*(1-w.qb)≤w.vmax) ∨ (1/2≤w.qa ∧ w.qa*(1-w.qa)≤w.vmax) ∨ 1/4≤w.vmax))
    ⟨(fun ⟨qa_pos,qa_le_qb,qb_lt_one,rho_pos,parent_lower,parent_upper,density,R_nonneg,R_bound,variance_bound,variance_cap⟩=>⟨qa_pos,qa_le_qb,qb_lt_one,rho_pos,parent_lower,parent_upper,density,R_nonneg,R_bound,variance_bound,variance_cap⟩),
      (fun h=>⟨h.qa_pos,h.qa_le_qb,h.qb_lt_one,h.rho_pos,h.parent_lower,h.parent_upper,h.density,h.R_nonneg,h.R_bound,h.variance_bound,h.variance_cap⟩)⟩

def Window.check (w : Window) : Bool := decide w.Valid
variable {V : Type*} [DecidableEq V]

theorem Window.activity_bounds (w : Window) (hw : w.Valid) {z : ℝ}
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    (w.lower:ℝ)≤z ∧ z≤(w.upper:ℝ) := by
  have hqb : (w.qb:ℝ)<1 := by exact_mod_cast hw.qb_lt_one
  have hqa : (w.qa:ℝ)<1 := by exact_mod_cast hw.qa_le_qb.trans_lt hw.qb_lt_one
  have hlo := (le_div_iff₀ (by positivity : 0<1+z)).mp hq.1
  have hhi := (div_le_iff₀ (by positivity : 0<1+z)).mp hq.2
  simp only [Window.lower,Window.upper,Rat.cast_div,Rat.cast_sub,Rat.cast_one]
  constructor
  · apply (div_le_iff₀ (by linarith : 0<1-(w.qa:ℝ))).mpr
    nlinarith
  · apply (le_div_iff₀ (by linarith : 0<1-(w.qb:ℝ))).mpr
    nlinarith

theorem Window.density (w : Window) (hw : w.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) {z : ℝ}
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    (w.rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z := by
  have hlo := (w.activity_bounds hw hz hq).1
  have hapos : (0:ℝ)<w.lower := by
    have hr : (0:ℚ)<w.lower := div_pos hw.qa_pos (sub_pos.mpr (hw.qa_le_qb.trans_lt hw.qb_lt_one))
    exact_mod_cast hr
  by_cases hh : (1:ℚ)≤w.lower
  · apply forest_density_of_upper_activity_certificate G hG S (by exact_mod_cast hh) hlo
      (by exact_mod_cast hw.rho_pos.le)
    have hc := hw.density
    rw [if_pos hh] at hc
    have hr := (Rat.cast_le (K:=ℝ)).mpr hc
    norm_num at hr ⊢
    exact hr
  · have hA : (43/100:ℝ)≤(max (nonnegative w.parent).A (43/100:ℚ):ℝ) := by
      have hr := (Rat.cast_le (K:=ℝ)).mpr (le_max_right (nonnegative w.parent).A (43/100:ℚ))
      norm_num at hr ⊢
    apply forest_central_density_of_lower_activity_certificate G hG S
      (A:=(max (nonnegative w.parent).A (43/100:ℚ):ℝ)) hapos
      (by exact_mod_cast le_of_not_ge hh) hlo hA hrank
    have hc := hw.density
    rw [if_neg hh] at hc
    have hr := (Rat.cast_le (K:=ℝ)).mpr hc
    norm_num at hr ⊢
    exact hr

theorem Window.available_variance (w : Window) (hw : w.Valid)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreAvailableVariance G S B z≤(w.D:ℝ)*hardCoreAvailableMean G S B z := by
  have hab := w.activity_bounds hw hz hq
  have hdensity := w.density hw G hG S hz hq hrank
  have hρq := MeanMatchedSourceBudget.density_le_probability_cap G S hz hS hdensity
  have hqa : (0:ℝ)<w.qa := by exact_mod_cast hw.qa_pos
  have hc := hw.variance_bound
  unfold Window.varianceCheck at hc
  cases hs : w.source with
  | inl j =>
    rw [hs] at hc
    have hP := AffineSource.Parameters.check_sound (AffineSourceLibrary.parameters_checked j)
    apply Stage350SourceBudget.affine_available_variance_le hB hG hz
      (b:=((AffineSourceLibrary.domain j).b:ℝ))
      (hab.2.trans (by exact_mod_cast hc.1)) (by exact_mod_cast hw.rho_pos) hρq hdensity
      (AffineSourceLibrary.parameters j).toReal hP.1 hP.2.1 (AffineSourceLibrary.source_valid j) hqa hq
    dsimp only at hc
    rcases hc.2 with h | h
    · apply Or.inl
      constructor
      · change (2*((AffineSourceLibrary.parameters j).A:ℝ)/(w.rho:ℝ)+((AffineSourceLibrary.parameters j).C:ℝ)-1)*(w.qb:ℝ)≤2*((AffineSourceLibrary.parameters j).A:ℝ)
        exact_mod_cast h.1
      · unfold Stage350SourceBudget.affineCoefficient
        change 1+(2*((AffineSourceLibrary.parameters j).A:ℝ)/(w.rho:ℝ)+((AffineSourceLibrary.parameters j).C:ℝ)-1)/(w.qb:ℝ)-
          ((AffineSourceLibrary.parameters j).A:ℝ)/(w.qb:ℝ)^2≤(w.D:ℝ)
        exact_mod_cast h.2
    · apply Or.inr
      constructor
      · change 2*((AffineSourceLibrary.parameters j).A:ℝ)≤(2*((AffineSourceLibrary.parameters j).A:ℝ)/(w.rho:ℝ)+((AffineSourceLibrary.parameters j).C:ℝ)-1)*(w.qa:ℝ)
        exact_mod_cast h.1
      · unfold Stage350SourceBudget.affineCoefficient
        change 1+(2*((AffineSourceLibrary.parameters j).A:ℝ)/(w.rho:ℝ)+((AffineSourceLibrary.parameters j).C:ℝ)-1)/(w.qa:ℝ)-
          ((AffineSourceLibrary.parameters j).A:ℝ)/(w.qa:ℝ)^2≤(w.D:ℝ)
        exact_mod_cast h.2
  | inr j =>
    rw [hs] at hc
    exact Stage350SourceBudget.marked_available_variance_le j hB hG
      ((by exact_mod_cast hc.1 : ((Stage350SourceBudget.markedRow j).lower:ℝ)≤w.lower).trans hab.1)
      (hab.2.trans (by exact_mod_cast hc.2.1)) hqa hq.1 (by exact_mod_cast hc.2.2)

theorem Window.centered_variance (w : Window) (hw : w.Valid)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    hardCoreLayerMeanVariance G S B z≤
      (w.R:ℝ)*(z/(1+z)*(1-z/(1+z)))*hardCoreAvailableMean G S B z := by
  have hab := w.activity_bounds hw hz hq
  have hv := valid w.parent
  have hs := SelectionSource.Parameters.check_sound (Stage900SourceTable.selection_checked (selectionIndex w.parent))
  have hlo : ((base w.parent).lower:ℝ)≤z :=
    (show ((base w.parent).lower:ℝ)≤w.lower by exact_mod_cast hv.selection_lower.trans hw.parent_lower).trans hab.1
  have hhi : z≤((base w.parent).upper:ℝ) := hab.2.trans
    (by exact_mod_cast hw.parent_upper.trans hv.selection_upper)
  have hselect := hB.variance_le_mass_of_selection_certificate hG
    (show (0:ℝ)<(base w.parent).lower by
      exact_mod_cast (Stage900SourceTable.valid (selectionIndex w.parent)).lower_pos)
    hlo hhi (selection w.parent).toReal hs.1 hs.2.1 hs.2.2
    (Stage900SourceTable.selection_valid (selectionIndex w.parent))
  have hc : ((selection w.parent).CJ:ℝ)+2*((selection w.parent).Cmu:ℝ)≤w.CW := by
    exact_mod_cast hv.CW_bound
  have hmass : 0≤hardCoreOccupiedMass G S B z := by
    rw [hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz]
    exact mul_nonneg (by positivity) (hardCoreAvailableMean_nonneg G S B hz.le)
  have hCJ := hs.2.1
  have hCmu := hs.2.2
  have hCW : (0:ℝ)≤w.CW := (by positivity : (0:ℝ)≤(selection w.parent).toReal.CJ+2*(selection w.parent).toReal.Cmu).trans hc
  apply MeanMatchedSourceBudget.centered_variance_bound hB.subset hB.independent hz hq.2
    (by exact_mod_cast hw.qb_lt_one) hCW (by exact_mod_cast hw.R_bound)
  exact hselect.trans (mul_le_mul_of_nonneg_right hc hmass)

theorem Window.variance_cap (w : Window) (hw : w.Valid) {q : ℝ}
    (hq : q∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) : q*(1-q)≤(w.vmax:ℝ) := by
  rcases hw.variance_cap with h | h | h
  · have hqb : (w.qb:ℝ)≤1/2 := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr h.1
      norm_num at hh
      exact hh
    have hc : (w.qb:ℝ)*(1-w.qb)≤w.vmax := by exact_mod_cast h.2
    have hp := mul_nonneg (sub_nonneg.mpr hq.2) (show 0≤1-(w.qb:ℝ)-q by linarith [hq.2])
    nlinarith
  · have hqa : (1/2:ℝ)≤w.qa := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr h.1
      norm_num at hh
      exact hh
    have hc : (w.qa:ℝ)*(1-w.qa)≤w.vmax := by exact_mod_cast h.2
    have hp := mul_nonneg (sub_nonneg.mpr hq.1) (show 0≤q+(w.qa:ℝ)-1 by linarith [hq.1])
    nlinarith
  · have hc : (1/4:ℝ)≤w.vmax := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr h
      norm_num at hh
      exact hh
    nlinarith [sq_nonneg (q-1/2)]

theorem Window.total_variance (w : Window) (hw : w.Valid)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ)) :
    hardCoreVariance G S z≤
      (z/(1+z)*(1-z/(1+z))+(w.R*w.vmax:ℚ))*hardCoreAvailableMean G S B z+0 := by
  have hc := w.centered_variance hw hB hG hz hq
  have hv := w.variance_cap hw hq
  have hm := hardCoreAvailableMean_nonneg G S B hz.le
  have hR : (0:ℝ)≤w.R := by exact_mod_cast hw.R_nonneg
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hR) hm
  have he := hardCoreVariance_eq_layer_variance G S B hB.subset hB.independent hz
  push_cast
  nlinarith

theorem Window.mean_lower (w : Window) (hw : w.Valid)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) (N : ℕ) (hn : N≤S.card) :
    (w.rho:ℝ)*N/(2*(w.qb:ℝ))≤hardCoreAvailableMean G S B z := by
  exact MeanMatchedSourceBudget.available_mean_lower hB hG hz
    (by exact_mod_cast hw.rho_pos) hq.2 N hn (w.density hw G hG S hz hq hrank)

structure RateCertificate where
  source : Fin 15
  retention : ℚ
  tilt : ℚ
  rate : ℚ
  lowerWitness : AffineTailRateCertificate.Certificate
  upperWitness : AffineTailRateCertificate.Certificate
  deriving Repr

def RateCertificate.Accepts (c : RateCertificate) (w : Window) : Prop :=
  w.upper≤(AffineSourceLibrary.domain c.source).b ∧
  0≤c.retention ∧ c.retention≤c.lowerWitness.uLower ∧
  c.lowerWitness.check (AffineSourceLibrary.parameters c.source).A
    (AffineSourceLibrary.parameters c.source).C w.rho 0 c.tilt w.qa c.rate=true ∧
  c.upperWitness.check (AffineSourceLibrary.parameters c.source).A
    (AffineSourceLibrary.parameters c.source).C w.rho 0 c.tilt w.qb c.rate=true
instance (c : RateCertificate) (w : Window) : Decidable (c.Accepts w) := by
  unfold RateCertificate.Accepts
  infer_instance

def RateCertificate.check (c : RateCertificate) (w : Window) : Bool := decide (c.Accepts w)

theorem RateCertificate.actual_laplace (c : RateCertificate) (w : Window)
    (hw : w.Valid) (hc : c.check w=true)
    {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hS : 0<S.card)
    (hq : z/(1+z)∈Set.Icc (w.qa:ℝ) (w.qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z c.retention≤
      Real.exp (-(c.rate:ℝ)*hardCoreAvailableMean G S B z) := by
  obtain ⟨hcap,ht,hte,hl,hh⟩ := (of_decide_eq_true hc : c.Accepts w)
  exact AffineSourceLaplaceRate.actual_laplace_of_certificates c.source
    c.lowerWitness c.upperWitness hl hh ht hte hw.qa_pos.le hw.qb_lt_one.le hB hG hz
    ((w.activity_bounds hw hz hq).2.trans (by exact_mod_cast hcap)) hS hq
    (w.density hw G hG S hz hq hrank)

#print axioms RateCertificate.actual_laplace

#print axioms Window.density
#print axioms Window.available_variance
#print axioms Window.centered_variance
#print axioms Window.total_variance
#print axioms Window.mean_lower
end ForestUnimodality.FiniteSourceWindow
