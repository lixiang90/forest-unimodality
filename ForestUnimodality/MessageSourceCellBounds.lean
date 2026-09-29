import ForestUnimodality.MessageLogPenalty
import ForestUnimodality.ExactLogCapacityMonotonicity
import ForestUnimodality.SelectionSourceCells

/-! Transcendental bounds for probability cells, independent of any old
relaxed-h envelope check. These helpers are shared by constant and spline
message-price sources. -/
namespace ForestUnimodality

theorem SelectionSource.Cell.capacity_bounds {c : SelectionSource.Cell}
    {D : ParametricSource.Domain} (hD : D.Valid)
    (hcap : c.CapacityAccepts D) (hleft : (0:ℝ)≤c.left) (hLr : (0:ℝ)≤c.L)
    {p : ℝ} (hp : 0<p) (hlp : (c.left:ℝ)≤p) (hpr : p≤(c.right:ℝ))
    (hpq : p<(D.b:ℝ)/(1+(D.b:ℝ))) :
    (c.L:ℝ)≤1/(p*sourceLogCapacity D.b p) ∧
      (c.H:ℝ)≤1/sourceOddsCapacity D.b (sourceLogCapacity D.b p) := by
  unfold SelectionSource.Cell.CapacityAccepts at hcap
  by_cases hl0 : c.left=0
  · rw [if_pos hl0] at hcap
    rcases hcap with ⟨hrq,hHz,hlog,hlo,hh⟩
    have hlogr := c.logCapacity.certificate.check_sound hlog
    push_cast at hlogr
    have hrrq : (c.right:ℝ)<(D.b:ℝ)/(1+(D.b:ℝ)) := by
      unfold SelectionSource.probabilityCap at hrq
      exact_mod_cast hrq
    have hlor : 1/(1-(c.right:ℝ))≤(c.logCapacity.lo:ℝ) := by exact_mod_cast hlo
    refine ⟨source_origin_capacity_lower hD.b_pos hp hpr hrrq
      (hlor.trans hlogr.1) hlogr.2 hLr (by exact_mod_cast hh),?_⟩
    rw [hHz,Rat.cast_zero]
    exact one_div_nonneg.mpr
      (sourceOddsCapacity_pos hD.b_pos (source_log_capacity_pos hD.b_pos hp hpq)).le
  · rw [if_neg hl0] at hcap
    rcases hcap with ⟨hlog,hLc,hjlo,hjhi,hH⟩
    have hlpos : (0:ℝ)<c.left := lt_of_le_of_ne hleft (Ne.symm (by exact_mod_cast hl0))
    have hlogr := (c.logCapacity.certificate.check_sound hlog).2
    push_cast at hlogr
    have hLc' : (c.L:ℝ)≤1/(D.K:ℝ) ∨ (c.L:ℝ)*((c.right:ℝ)*(c.logCapacity.hi:ℝ))≤1 := by
      rcases hLc with h|h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    exact source_cell_capacity_bounds_general c.segment hD.b_pos hD.K_pos hD.capacity
      hlpos hlp hpr hpq hlogr hLc' hLr (by exact_mod_cast hjlo)
      (by exact_mod_cast hjhi) (by exact_mod_cast hH)

/-- A directed lower bound for log(1/(1-p)) gives the safe upper Cauchy
price. A lower bound for log(1-p) would have the wrong direction. -/
theorem sourceExactH_upper_of_log_lower {p ell hh : ℝ}
    (hp : 0<p) (hp1 : p<1) (hhh : 0≤hh)
    (hlog : ell≤Real.log (1/(1-p))) (hprice : p≤hh*ell) :
    sourceExactH p≤hh := by
  have hd := neg_pos.mpr (Real.log_neg (sub_pos.mpr hp1) (by linarith))
  rw [Real.log_div one_ne_zero (sub_pos.mpr hp1).ne',Real.log_one,zero_sub] at hlog
  rw [sourceExactH,if_neg hp.ne']
  apply (div_le_iff₀ hd).mpr
  exact hprice.trans (mul_le_mul_of_nonneg_left hlog hhh)

theorem sourceExactH_cell_upper {left p hh : ℝ}
    (hl : 0≤left) (hlp : left≤p) (hp1 : p<1) (hleft : sourceExactH left≤hh) :
    sourceExactH p≤hh :=
  (sourceExactH_antitone ⟨hl,hlp.trans_lt hp1⟩ ⟨hl.trans hlp,hp1⟩ hlp).trans hleft

theorem sourceLogReference_upper {lower p lpUpper lcLower laLower : ℝ}
    (hp : Real.log p≤lpUpper) (hc : lcLower≤Real.log (1-p))
    (ha : laLower≤Real.log lower) :
    sourceLogReference lower p≤lpUpper-2*lcLower-laLower := by
  unfold sourceLogReference
  linarith

theorem sourceLogPenalty_cell_lower {lower Dn ell p ph gUpper bound : ℝ}
    (hlower : 0<lower) (hell : 0≤ell)
    (hprice : 0≤Dn+ell*(1+Real.sqrt 2-Real.log ((1+Real.sqrt 2)/(2*lower))))
    (hp : 0<p) (hpph : p≤ph) (hph1 : ph<1)
    (hg : sourceLogReference lower ph≤gUpper)
    (hbound : bound*ph≤Dn-ell*gUpper) :
    bound≤sourceLogPenalty lower Dn ell p := by
  have hph := hp.trans_le hpph
  have hendpoint : bound≤sourceLogPenalty lower Dn ell ph := by
    unfold sourceLogPenalty
    apply (le_div_iff₀ hph).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg hell]
  exact hendpoint.trans (sourceLogPenalty_antitone hlower hell hprice
    ⟨hp,hpph.trans_lt hph1⟩ ⟨hph,hph1⟩ hpph)

#print axioms SelectionSource.Cell.capacity_bounds
#print axioms sourceExactH_upper_of_log_lower
#print axioms sourceLogPenalty_cell_lower
end ForestUnimodality
