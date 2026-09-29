import ForestUnimodality.SignedGaussian350Data.Beta60
import ForestUnimodality.SignedGaussian350Data.Beta65
import ForestUnimodality.ShiftedCurvatureErrorLayerBudget
import ForestUnimodality.CurvatureBudgetNormalization

/-! The complete stage-350 central budget. The normalization factor is
frozen conservatively at the starting mean; every charge decreases over
the entire remaining half-line. -/
namespace ForestUnimodality.Stage350CurvatureBudget
open Real Set Finset PointMassBudgetMonotonicity PointMassErrorEnvelope UnboundedBudget

noncomputable def beta (large : Bool) : ℝ :=
  if large then SignedGaussian350Data.Beta65.beta else SignedGaussian350Data.Beta60.beta
noncomputable def B (large : Bool) : ℝ :=
  if large then SignedGaussian350Data.Beta65.B else SignedGaussian350Data.Beta60.B
noncomputable def prices (large : Bool) : ℕ→ℝ :=
  if large then SignedGaussian350Data.Beta65.prices else SignedGaussian350Data.Beta60.prices
noncomputable def profileCut (large : Bool) (i : ℕ) : ℝ :=
  7/20+(beta large-7/20)*(i:ℝ)/40
noncomputable def cut (i : ℕ) : ℝ := ((i:ℝ)+1)*7/480

structure Parameters where
  a : ℝ
  b : ℝ
  start : ℝ
  vmin : ℝ
  vmax : ℝ
  eta : ℝ
  R : ℝ
  D : ℝ
  largeBeta : Bool
  gapRate : Fin 40→ℝ
  badRate : Fin 24→ℝ

noncomputable def shiftFactor (m c : ℝ) : ℝ := m*sqrt m/((m+c)*sqrt (m+c))
noncomputable def gapCost (p : Parameters) (m : ℝ) : ℝ :=
  ∑i : Fin 40,(prices p.largeBeta i.val-prices p.largeBeta (i.val+1))*exp (-p.gapRate i*m)
noncomputable def main (p : Parameters) (m : ℝ) : ℝ :=
  exp (-(9/20:ℝ))*(209/200-(21/20)*p.R)-B p.largeBeta*p.D/m-gapCost p m
noncomputable def cubic (p : Parameters) (m : ℝ) : ℝ :=
  (4*sqrt (2*Real.pi)/(3*Real.pi))*p.eta*rho (7/20) m^3*
    momentFactor 2 (7/20) p.D m/sqrt (p.vmin*m)
noncomputable def quartic (p : Parameters) (m : ℝ) : ℝ :=
  (5/16)*rho (7/20) m^(7/2:ℝ)*momentFactor (5/2) (7/20) p.D m/(p.vmin*m)
noncomputable def triangular (p : Parameters) (m : ℝ) : ℝ :=
  momentFactor (7/2) (7/20) p.D m/(96*(p.vmin*m)^2)
noncomputable def tail (p : Parameters) (m : ℝ) : ℝ :=
  sqrt (2*Real.pi)*p.vmax*sqrt p.vmax*
    ((3/p.vmin)*powerExpCost (1/2) ((3/2)*p.vmin) m+
      (1/p.vmin^2)*powerExpCost (-1/2) ((3/2)*p.vmin) m)
noncomputable def bad (p : Parameters) (m : ℝ) : ℝ :=
  sqrt (2*Real.pi)*p.vmax*sqrt p.vmax*powerExpCost (3/2) (p.badRate 0) m+
    ((cut 22)^(-(3/2:ℝ))*exp (-p.badRate 23*m)+
      ∑i : Fin 22,((cut i.val)^(-(3/2:ℝ))-(cut (i.val+1))^(-(3/2:ℝ)))*
        exp (-p.badRate ⟨i.val+1,by omega⟩*m))
noncomputable def budget (p : Parameters) (m : ℝ) : ℝ :=
  shiftFactor p.start (1/(6*p.vmin))*main p m-
    cubic p m-quartic p m-triangular p m-tail p m-bad p m

structure Parameters.Valid (p : Parameters) : Prop where
  start_large : 6≤p.start
  vmin_pos : 0<p.vmin
  vmax_pos : 0<p.vmax
  eta_nonneg : 0≤p.eta
  R_nonneg : 0≤p.R
  D_nonneg : 0≤p.D
  gapRate_nonneg : ∀i,0≤p.gapRate i
  badRate_nonneg : ∀i,0≤p.badRate i
  bottom_threshold : 3/2≤p.badRate 0*p.start
  tail_threshold : 1/2≤((3/2)*p.vmin)*p.start

theorem B_pos (large : Bool) : 0<B large := by
  cases large <;> norm_num [B,SignedGaussian350Data.Beta60.B,SignedGaussian350Data.Beta65.B]
theorem prices_step (large : Bool) (i : ℕ) (hi : i≤39) : prices large (i+1)≤prices large i := by
  by_cases hl : i<39
  · cases large
    · exact SignedGaussian350Data.Beta60.prices_decreasing i hl
    · exact SignedGaussian350Data.Beta65.prices_decreasing i hl
  · have he : i=39 := by omega
    subst i
    cases large
    · exact SignedGaussian350Data.Beta60.prices_nonneg 39 le_rfl
    · exact SignedGaussian350Data.Beta65.prices_nonneg 39 le_rfl
theorem cut_pos (i : ℕ) : 0<cut i := by unfold cut; positivity
theorem cut_step (i : ℕ) : cut i≤cut (i+1) := by unfold cut; push_cast; linarith
theorem cut_price_step (i : ℕ) : (cut (i+1))^(-(3/2:ℝ))≤(cut i)^(-(3/2:ℝ)) :=
  rpow_le_rpow_of_nonpos (cut_pos i) (cut_step i) (by norm_num)

theorem shiftFactor_pos {m c : ℝ} (hm : 0<m) (hc : 0≤c) : 0<shiftFactor m c := by
  unfold shiftFactor
  have hmc : 0<m+c := by linarith
  positivity
theorem shiftFactor_mono {x y c : ℝ} (hx : 0<x) (hxy : x≤y) (hc : 0≤c) :
    shiftFactor x c≤shiftFactor y c := by
  have hy : 0<y := hx.trans_le hxy
  have hxc : 0<x+c := by linarith
  have hyc : 0<y+c := by linarith
  have hr : x/(x+c)≤y/(y+c) := by
    apply (div_le_div_iff₀ hxc hyc).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hc]
  have he (m : ℝ) (hm : 0<m) : shiftFactor m c=(m/(m+c))*sqrt (m/(m+c)) := by
    unfold shiftFactor
    rw [sqrt_div hm.le]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he x hx,he y hy]
  exact mul_le_mul hr (sqrt_le_sqrt hr) (sqrt_nonneg _) (by positivity)

theorem gapCost_antitone {p : Parameters} (h : p.Valid) {x y : ℝ} (hxy : x≤y) :
    gapCost p y≤gapCost p x := by
  apply sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (prices_step _ _ (by omega)))
  apply exp_le_exp.mpr
  nlinarith [h.gapRate_nonneg i]

theorem main_monotone {p : Parameters} (h : p.Valid) {x y : ℝ} (hx : p.start≤x) (hxy : x≤y) :
    main p x≤main p y := by
  have hx0 : 0<x := by linarith [h.start_large]
  have hd:=div_le_div_of_nonneg_left (mul_nonneg (B_pos p.largeBeta).le h.D_nonneg) hx0 hxy
  exact sub_le_sub (sub_le_sub_left hd _) (gapCost_antitone h hxy)

theorem cubic_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : cubic p y≤cubic p x := by
  have hv:=h.vmin_pos
  have heta:=h.eta_nonneg
  have hx0 : 0<x := by linarith [h.start_large]
  have hy0:=hx0.trans_le hxy
  have hax : 1<(7/20:ℝ)*x := by linarith [h.start_large]
  have hay : 1<(7/20:ℝ)*y := by linarith
  have hr' := bridgeRatio_antitone (by norm_num : (0:ℝ)<7/20) hax hxy
  change rho (7/20) y≤rho (7/20) x at hr'
  have hj := momentFactor_antitone (p:=2) (by norm_num) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hx0 hxy
  have hp:=mul_le_mul (pow_le_pow_left₀ (rho_pos hay).le hr' 3) hj
    (momentFactor_nonneg (by norm_num) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hy0)
    (pow_nonneg (rho_pos hax).le 3)
  have hyj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hy0
  have hxj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hx0
  have hry:=rho_pos hay
  have hrx:=rho_pos hax
  unfold cubic
  apply div_le_div₀ (by positivity) ?_ (by positivity) (sqrt_le_sqrt (by nlinarith [h.vmin_pos]))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
    (show 0≤(4*sqrt (2*Real.pi)/(3*Real.pi))*p.eta by positivity)

theorem quartic_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : quartic p y≤quartic p x := by
  have hv:=h.vmin_pos
  have hx0 : 0<x := by linarith [h.start_large]
  have hy0:=hx0.trans_le hxy
  have hax : 1<(7/20:ℝ)*x := by linarith [h.start_large]
  have hay : 1<(7/20:ℝ)*y := by linarith
  have hr := bridgeRatio_antitone (by norm_num : (0:ℝ)<7/20) hax hxy
  change rho (7/20) y≤rho (7/20) x at hr
  have hj := momentFactor_antitone (p:=5/2) (by norm_num) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hx0 hxy
  have hp:=rpow_le_rpow (rho_pos hay).le hr (by norm_num : (0:ℝ)≤7/2)
  have hyj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤5/2) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hy0
  have hxj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤5/2) (by norm_num : (0:ℝ)<7/20) h.D_nonneg hx0
  have hry:=rho_pos hay
  have hrx:=rho_pos hax
  unfold quartic
  apply div_le_div₀ (by positivity) ?_ (by positivity) (by nlinarith [h.vmin_pos])
  exact mul_le_mul (by linarith) hj hyj (by positivity)

theorem triangular_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : triangular p y≤triangular p x := by
  have hv:=h.vmin_pos
  have hx0 : 0<x := by linarith [h.start_large]
  have hy0:=hx0.trans_le hxy
  unfold triangular
  apply div_le_div₀ (momentFactor_nonneg (by norm_num) (by norm_num) h.D_nonneg hx0)
    (momentFactor_antitone (by norm_num) (by norm_num) h.D_nonneg hx0 hxy) (by positivity)
  gcongr

theorem tail_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : tail p y≤tail p x := by
  have hs : 0<p.start := by linarith [h.start_large]
  have hv:=h.vmin_pos
  have hV:=h.vmax_pos
  have h1:=powerExpCost_antitoneOn hs (show 0≤(3/2)*p.vmin by positivity) h.tail_threshold
  have h2:=powerExpCost_antitoneOn hs (show 0≤(3/2)*p.vmin by positivity)
    (show (-1/2:ℝ)≤((3/2)*p.vmin)*p.start by linarith [h.tail_threshold])
  unfold tail
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (h1 hx (hx.trans hxy) hxy) (by positivity))
    (mul_le_mul_of_nonneg_left (h2 hx (hx.trans hxy) hxy) (by positivity))

theorem bad_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : bad p y≤bad p x := by
  have hs : 0<p.start := by linarith [h.start_large]
  have hV:=h.vmax_pos
  have h0:=powerExpCost_antitoneOn hs (h.badRate_nonneg 0) h.bottom_threshold
  have he (i : Fin 24) : exp (-p.badRate i*y)≤exp (-p.badRate i*x) := by
    apply exp_le_exp.mpr
    nlinarith [h.badRate_nonneg i]
  unfold bad
  apply add_le_add (mul_le_mul_of_nonneg_left (h0 hx (hx.trans hxy) hxy) (by positivity))
  apply add_le_add (mul_le_mul_of_nonneg_left (he 23) (rpow_nonneg (cut_pos 22).le _))
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (he ⟨i.val+1,by omega⟩) (sub_nonneg.mpr (cut_price_step i.val))

theorem budget_monotoneOn {p : Parameters} (h : p.Valid) : MonotoneOn (budget p) (Ici p.start) := by
  have hs : 0<p.start := by linarith [h.start_large]
  have hv:=h.vmin_pos
  intro x hx y hy hxy
  unfold budget
  exact sub_le_sub (sub_le_sub (sub_le_sub (sub_le_sub (sub_le_sub
    (mul_le_mul_of_nonneg_left (main_monotone h hx hxy) (shiftFactor_pos hs (by positivity)).le)
    (cubic_antitone h hx hxy)) (quartic_antitone h hx hxy)) (triangular_antitone h hx hxy))
    (tail_antitone h hx hxy)) (bad_antitone h hx hxy)

theorem budget_positive {p : Parameters} (h : p.Valid) (hstart : 0<budget p p.start)
    {m : ℝ} (hm : p.start≤m) : 0<budget p m :=
  hstart.trans_le (budget_monotoneOn h (by simp) hm hm)

#print axioms shiftFactor_mono
#print axioms budget_monotoneOn
#print axioms budget_positive
end ForestUnimodality.Stage350CurvatureBudget
