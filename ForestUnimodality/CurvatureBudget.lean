import ForestUnimodality.PointMassBudgetMonotonicity
import ForestUnimodality.PointMassSqrtNormalization

/-! The actual central Gaussian budget continued over the complete half-line.
The sixteen bad-layer cutoffs are fixed fractions, independent of graph order. -/
namespace ForestUnimodality.CurvatureBudget
open Set Finset PointMassBudgetMonotonicity PointMassErrorEnvelope UnboundedBudget

structure Parameters where
  a : ℝ
  b : ℝ
  start : ℝ
  vmin : ℝ
  vmax : ℝ
  eta : ℝ
  R : ℝ
  D : ℝ
  rate : Fin 16 → ℝ

noncomputable def cut (i : ℕ) : ℝ := ((i:ℝ)+1)/48

noncomputable def cubic (p : Parameters) (m : ℝ) : ℝ :=
  (4*Real.sqrt (2*Real.pi)/(3*Real.pi))*p.eta*rho (1/3) m^3*
    momentFactor 2 (1/3) p.D m / Real.sqrt (p.vmin*m)

noncomputable def quartic (p : Parameters) (m : ℝ) : ℝ :=
  ((5/16)*rho (1/3) m^(7/2:ℝ)+1/4)*momentFactor (5/2) (1/3) p.D m/(p.vmin*m)

noncomputable def tail (p : Parameters) (m : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*p.vmax*Real.sqrt p.vmax*
    ((3/p.vmin)*powerExpCost (1/2) ((3/2)*p.vmin) m+
      (1/p.vmin^2)*powerExpCost (-1/2) ((3/2)*p.vmin) m)

noncomputable def bad (p : Parameters) (m : ℝ) : ℝ :=
  Real.sqrt (2*Real.pi)*p.vmax*Real.sqrt p.vmax*powerExpCost (3/2) (p.rate 0) m+
    (Real.pi^3/8)*∑i : Fin 15,(cut i.val)^(-(3/2:ℝ))*Real.exp (-p.rate i.succ*m)

noncomputable def budget (p : Parameters) (m : ℝ) : ℝ :=
  Real.exp (-(2/5:ℝ))*(27/25-(11/10)*p.R)-(4813/1000)*p.D/m-
    cubic p m-quartic p m-tail p m-bad p m

structure Parameters.Valid (p : Parameters) : Prop where
  start_pos : 0<p.start
  start_large : 6≤p.start
  vmin_pos : 0<p.vmin
  vmax_pos : 0<p.vmax
  eta_nonneg : 0≤p.eta
  D_nonneg : 0≤p.D
  rate_nonneg : ∀i,0≤p.rate i
  bottom_threshold : 3/2≤p.rate 0*p.start
  tail_threshold : 1/2≤((3/2)*p.vmin)*p.start

theorem cut_pos (i : ℕ) : 0<cut i := by unfold cut; positivity

theorem cubic_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : cubic p y≤cubic p x := by
  have hv:=h.vmin_pos
  have heta:=h.eta_nonneg
  have hx0:=h.start_pos.trans_le hx
  have hy0:=hx0.trans_le hxy
  have hax : 1<(1/3:ℝ)*x := by linarith [h.start_large]
  have hay : 1<(1/3:ℝ)*y := by linarith
  have hr := bridgeRatio_antitone (by norm_num : (0:ℝ)<1/3) hax hxy
  change rho (1/3) y≤rho (1/3) x at hr
  have hj := momentFactor_antitone (p:=2) (by norm_num) (by norm_num : (0:ℝ)<1/3)
    h.D_nonneg hx0 hxy
  have hp:=mul_le_mul (pow_le_pow_left₀ (rho_pos hay).le hr 3) hj
    (momentFactor_nonneg (by norm_num) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hy0)
    (pow_nonneg (rho_pos hax).le 3)
  have hyj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hy0
  have hxj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hx0
  have hry:=rho_pos hay
  have hrx:=rho_pos hax
  unfold cubic
  apply div_le_div₀ (by positivity) ?_ (by positivity) (Real.sqrt_le_sqrt (by nlinarith [h.vmin_pos]))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
    (show 0≤(4*Real.sqrt (2*Real.pi)/(3*Real.pi))*p.eta by positivity)

theorem quartic_antitone {p : Parameters} (h : p.Valid) {x y : ℝ}
    (hx : p.start≤x) (hxy : x≤y) : quartic p y≤quartic p x := by
  have hv:=h.vmin_pos
  have hx0:=h.start_pos.trans_le hx
  have hy0:=hx0.trans_le hxy
  have hax : 1<(1/3:ℝ)*x := by linarith [h.start_large]
  have hay : 1<(1/3:ℝ)*y := by linarith
  have hr := bridgeRatio_antitone (by norm_num : (0:ℝ)<1/3) hax hxy
  change rho (1/3) y≤rho (1/3) x at hr
  have hj := momentFactor_antitone (p:=5/2) (by norm_num) (by norm_num : (0:ℝ)<1/3)
    h.D_nonneg hx0 hxy
  have hp:=Real.rpow_le_rpow (rho_pos hay).le hr (by norm_num : (0:ℝ)≤7/2)
  have hyj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤5/2) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hy0
  have hxj:=momentFactor_nonneg (by norm_num : (0:ℝ)≤5/2) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hx0
  have hry:=rho_pos hay
  have hrx:=rho_pos hax
  unfold quartic
  apply div_le_div₀ (by positivity) ?_ (by positivity) (by nlinarith [h.vmin_pos])
  exact mul_le_mul (by linarith) hj
    (momentFactor_nonneg (by norm_num) (by norm_num : (0:ℝ)<1/3) h.D_nonneg hy0)
    (by positivity)

theorem tail_antitoneOn {p : Parameters} (h : p.Valid) : AntitoneOn (tail p) (Ici p.start) := by
  have hv:=h.vmin_pos
  have hV:=h.vmax_pos
  have h1:=powerExpCost_antitoneOn h.start_pos (show 0≤(3/2)*p.vmin by positivity) h.tail_threshold
  have h2:=powerExpCost_antitoneOn h.start_pos (show 0≤(3/2)*p.vmin by positivity)
    (show (-1/2:ℝ)≤((3/2)*p.vmin)*p.start by linarith [h.tail_threshold])
  intro x hx y hy hxy
  unfold tail
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left (h1 hx hy hxy) (by positivity))
    (mul_le_mul_of_nonneg_left (h2 hx hy hxy) (by positivity))

theorem bad_antitoneOn {p : Parameters} (h : p.Valid) : AntitoneOn (bad p) (Ici p.start) := by
  have hV:=h.vmax_pos
  have h0:=powerExpCost_antitoneOn h.start_pos (h.rate_nonneg 0) h.bottom_threshold
  intro x hx y hy hxy
  unfold bad
  apply add_le_add (mul_le_mul_of_nonneg_left (h0 hx hy hxy) (by positivity))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (cut_pos i.val).le _)
  apply Real.exp_le_exp.mpr
  nlinarith [h.rate_nonneg i.succ]

theorem budget_monotoneOn {p : Parameters} (h : p.Valid) : MonotoneOn (budget p) (Ici p.start) := by
  have hD:=h.D_nonneg
  intro x hx y hy hxy
  have hd : (4813/1000)*p.D/y≤(4813/1000)*p.D/x :=
    div_le_div_of_nonneg_left (by positivity) (h.start_pos.trans_le hx) hxy
  unfold budget
  exact sub_le_sub (sub_le_sub (sub_le_sub (sub_le_sub (sub_le_sub_left hd _)
    (cubic_antitone h hx hxy)) (quartic_antitone h hx hxy))
    (tail_antitoneOn h hx hy hxy)) (bad_antitoneOn h hx hy hxy)

theorem budget_positive {p : Parameters} (h : p.Valid) (hstart : 0<budget p p.start)
    {m : ℝ} (hm : p.start≤m) : 0<budget p m :=
  hstart.trans_le (budget_monotoneOn h (by simp) hm hm)

#print axioms budget_monotoneOn
#print axioms budget_positive
end ForestUnimodality.CurvatureBudget
