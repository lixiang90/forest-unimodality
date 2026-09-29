import ForestUnimodality.NonnegativeSourceBounds
import ForestUnimodality.SourceScalarCells
import ForestUnimodality.SourceIntervalCoverage

/-! Exact rational certificates for arbitrary nonnegative source weights.
The first probability cell includes every p>0 down to zero analytically. -/
namespace ForestUnimodality.NonnegativeSource

structure Parameters where
  b : ℚ
  A : ℚ
  u : ℚ
  v : ℚ
  K : ℚ
  kExp : ExpEnclosure.PowerCertificate
  kExpLo : ℚ
  kExpHi : ℚ

def Parameters.q (P : Parameters) : ℚ := P.b/(1+P.b)

def Parameters.Accepts (P : Parameters) : Prop :=
  0<P.b ∧ 0≤P.A ∧ 0≤P.u ∧ 0≤P.v ∧ 0<P.K ∧
  P.kExp.check (1+P.K) P.kExpLo P.kExpHi=true ∧ P.b≤P.K*P.kExpLo ∧
  (1-P.q)+P.u*(1-P.q/2)≤P.A/P.q

instance instDecidableParametersAccepts (P : Parameters) : Decidable P.Accepts := by
  unfold Parameters.Accepts
  infer_instance

def Parameters.check (P : Parameters) : Bool := decide P.Accepts

structure Parameters.Valid (P : Parameters) : Prop where
  b_pos : 0<(P.b:ℝ)
  A_nonneg : 0≤(P.A:ℝ)
  u_nonneg : 0≤(P.u:ℝ)
  v_nonneg : 0≤(P.v:ℝ)
  K_pos : 0<(P.K:ℝ)
  capacity : (P.b:ℝ)≤P.K*Real.exp (1+(P.K:ℝ))
  leaf : (1-(P.q:ℝ))+(P.u:ℝ)*(1-(P.q:ℝ)/2)≤(P.A:ℝ)/(P.q:ℝ)

theorem Parameters.check_sound {P : Parameters} (hc : P.check=true) : P.Valid := by
  have hh : P.Accepts := of_decide_eq_true hc
  rcases hh with ⟨hb,hA,hu,hv,hK,he,hcap,hleaf⟩
  refine ⟨by exact_mod_cast hb, by exact_mod_cast hA, by exact_mod_cast hu,
    by exact_mod_cast hv, by exact_mod_cast hK, ?_, by exact_mod_cast hleaf⟩
  have hexp := (P.kExp.check_sound he).1
  push_cast at hexp
  have hcapr : (P.b:ℝ)≤(P.K:ℝ)*(P.kExpLo:ℝ) := by exact_mod_cast hcap
  exact hcapr.trans (mul_le_mul_of_nonneg_left hexp (by exact_mod_cast hK.le))

structure Cell where
  left : ℚ
  right : ℚ
  L : ℚ
  E : ℚ
  segment : ℕ
  logCapacity : SourceLogWitness

def Cell.EtaAccepts (c : Cell) (P : Parameters) : Prop :=
  (1+P.b)^c.segment≤P.b*(1-c.left)/c.left ∧
  P.b*(1-c.left)/c.left<(1+P.b)^(c.segment+1) ∧
  c.E≤1/((1+P.b*(1-c.left))*((c.segment:ℚ)*P.b+
    (P.b*(1-c.left)/c.left)/(1+P.b)^c.segment-1))

def Cell.CapacityAccepts (c : Cell) (P : Parameters) : Prop :=
  if c.left=0 then
    c.right<P.q ∧ c.E=0 ∧ c.logCapacity.check (P.b*(1-c.right)/c.right)=true ∧
    1/(1-c.right)≤c.logCapacity.lo ∧ c.L*(c.right*c.logCapacity.hi)≤1
  else
    c.logCapacity.check (P.b*(1-c.left)/c.left)=true ∧ c.EtaAccepts P ∧
    (c.L≤1/P.K ∨ c.L*(c.right*c.logCapacity.hi)≤1)

def Cell.Accepts (c : Cell) (P : Parameters) : Prop :=
  0≤c.left ∧ c.left<c.right ∧ c.right≤P.q ∧ 0≤c.L ∧ 0≤c.E ∧
  c.CapacityAccepts P ∧
  0≤c.E+P.u*c.L-((1-c.left)+P.v*(1-c.left/2)) ∧
  0≤P.A/c.right-((1-c.left)+P.u*(1-c.left/2)) ∧
  0<c.E+P.v*c.L-((1-c.left)+P.u*(1-c.left/2)) ∧
  ((1-c.left)+P.u*(1-c.left/2))^2≤
    (P.A/c.right-((1-c.left)+P.u*(1-c.left/2)))*
    (c.E+P.v*c.L-((1-c.left)+P.u*(1-c.left/2)))

instance instDecidableCellAccepts (c : Cell) (P : Parameters) : Decidable (c.Accepts P) := by
  unfold Cell.Accepts Cell.CapacityAccepts Cell.EtaAccepts
  infer_instance

def Cell.check (c : Cell) (P : Parameters) : Bool := decide (c.Accepts P)

theorem Cell.check_sound {c : Cell} {P : Parameters} (hc : c.check P=true) (hP : P.Valid)
    {p z : ℝ} (hp : 0<p) (hlp : (c.left:ℝ)≤p) (hpr : p≤(c.right:ℝ))
    (hpq : p<(P.b:ℝ)/(1+(P.b:ℝ))) :
    0≤nonnegativeSourceHomogeneous P.b P.A P.u P.v p 1 z := by
  have hc' : c.Accepts P := of_decide_eq_true hc
  rcases hc' with ⟨hl,hlr,hrq,hL,hE,hcap,hn,hc0,hc2,hdisc⟩
  have hleft : (0:ℝ)≤c.left := by exact_mod_cast hl
  have hright : (0:ℝ)<c.right := hp.trans_le hpr
  have hrightq : (c.right:ℝ)≤(P.b:ℝ)/(1+(P.b:ℝ)) := by
    unfold Parameters.q at hrq
    exact_mod_cast hrq
  have hleft1 : (c.left:ℝ)<1 := (hlp.trans_lt hpq).trans
    ((div_lt_one (by linarith [hP.b_pos] : 0<1+(P.b:ℝ))).mpr (by linarith))
  have hLr : (0:ℝ)≤c.L := by exact_mod_cast hL
  have hEr : (0:ℝ)≤c.E := by exact_mod_cast hE
  have hcapacities : (c.L:ℝ)≤1/(p*sourceLogCapacity P.b p) ∧ (c.E:ℝ)≤nonnegativeSourceEta P.b p := by
    unfold Cell.CapacityAccepts at hcap
    by_cases hl0 : c.left=0
    · rw [if_pos hl0] at hcap
      rcases hcap with ⟨hrq',hEz,hlog,hlo,hh⟩
      have hlogr := c.logCapacity.certificate.check_sound hlog
      push_cast at hlogr
      have hrrq : (c.right:ℝ)<(P.b:ℝ)/(1+(P.b:ℝ)) := by
        unfold Parameters.q at hrq'
        exact_mod_cast hrq'
      have hlor : 1/(1-(c.right:ℝ))≤(c.logCapacity.lo:ℝ) := by exact_mod_cast hlo
      refine ⟨source_origin_capacity_lower hP.b_pos hp hpr hrrq (hlor.trans hlogr.1) hlogr.2 hLr
        (by exact_mod_cast hh), ?_⟩
      simpa only [hEz, Rat.cast_zero] using nonnegativeSourceEta_nonneg hP.b_pos hp hpq
    · rw [if_neg hl0] at hcap
      rcases hcap with ⟨hlog,⟨hjlo,hjhi,hEta⟩,hLc⟩
      have hlpos : (0:ℝ)<c.left := by exact_mod_cast lt_of_le_of_ne hl (Ne.symm hl0)
      have hlogr := (c.logCapacity.certificate.check_sound hlog).2
      push_cast at hlogr
      have hLc' : (c.L:ℝ)≤1/(P.K:ℝ) ∨ (c.L:ℝ)*((c.right:ℝ)*(c.logCapacity.hi:ℝ))≤1 := by
        rcases hLc with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      have hfirst := (source_cell_capacity_bounds_general (H:=0) c.segment hP.b_pos hP.K_pos hP.capacity
        hlpos hlp hpr hpq hlogr hLc' hLr (by exact_mod_cast hjlo) (by exact_mod_cast hjhi)
        (by simp)).1
      refine ⟨hfirst, ?_⟩
      apply le_trans ?_ (nonnegativeSourceEta_mono hP.b_pos hlpos hlp hpq)
      rw [nonnegativeSourceEta_log_piece hP.b_pos c.segment (by exact_mod_cast hjlo) (by exact_mod_cast hjhi)]
      exact_mod_cast hEta
  have henv := nonnegativeSourceEnvelope_nonneg (mass:=(P.A:ℝ)/(c.right:ℝ))
    (E:=(c.E:ℝ)) (L:=(c.L:ℝ)) (dd:=1-(c.left:ℝ)) (hh:=1-(c.left:ℝ)/2)
    (u:=(P.u:ℝ)) (v:=(P.v:ℝ)) (div_nonneg hP.A_nonneg hright.le) hEr hLr
    (by linarith) (by linarith) hP.u_nonneg hP.v_nonneg
    (by exact_mod_cast hn) (by exact_mod_cast hc0) (by exact_mod_cast hc2) (by exact_mod_cast hdisc) z
  exact henv.trans (nonnegativeSourceEnvelope_le hp hpr hP.A_nonneg hP.u_nonneg hP.v_nonneg
    hcapacities.2 hcapacities.1 (by linarith) (by linarith))

theorem Parameters.leaf_sound {P : Parameters} (hP : P.Valid) :
    0≤nonnegativeSourceHomogeneous P.b P.A P.u P.v (P.q:ℝ) 1 1 := by
  simp only [nonnegativeSourceHomogeneous, one_pow, mul_one, sub_self, max_self,
    zero_pow (by decide : 2≠0), mul_zero, max_eq_right (by norm_num : (0:ℝ)≤1),
    max_eq_left (by norm_num : -(1:ℝ)≤0), zero_sub, add_zero]
  linarith [hP.leaf]

theorem sourceRowValid_of_cells (P : Parameters) (hP : P.Valid) (cells : List Cell)
    (hchecks : cells.all (fun c=>c.check P)=true)
    (hcover : SourceIntervalCoverage.check Cell.left Cell.right 0 P.q cells=true) :
    NonnegativeSourceRowValid P.b P.A P.u P.v := by
  intro p z hp hpq hend
  have hq : (P.q:ℝ)=(P.b:ℝ)/(1+(P.b:ℝ)) := by simp [Parameters.q]
  by_cases he : p=(P.q:ℝ)
  · have hz := hend (he.trans hq)
    subst p
    subst z
    exact Parameters.leaf_sound hP
  · have hpq' : p<(P.b:ℝ)/(1+(P.b:ℝ)) := lt_of_le_of_ne hpq (fun hh=>he (hh.trans hq.symm))
    obtain ⟨c,hmem,hlo,hhi⟩ := SourceIntervalCoverage.check_sound Cell.left Cell.right hcover
      (p:=p) (by simpa only [Rat.cast_zero] using hp) (hq.symm ▸ hpq)
    exact Cell.check_sound ((List.all_eq_true.mp hchecks) c hmem) hP hp hlo hhi hpq'

#print axioms Cell.check_sound
#print axioms sourceRowValid_of_cells
end ForestUnimodality.NonnegativeSource
