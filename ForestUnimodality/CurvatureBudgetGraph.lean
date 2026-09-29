import ForestUnimodality.CurvatureBudgetNormalization
import ForestUnimodality.SignedGaussianLayerBudget

/-! One actual layer law for the central main term, Fourier error and all
sixteen bad-event charges. Statistical assumptions are discharged by the
stage-specific source table, separately from this generic bridge. -/
namespace ForestUnimodality.CurvatureBudgetGraph
open Finset Set CurvatureBudget CurvatureErrorLayerBudget
open PointMassSqrtNormalization UnboundedBudget
variable {V : Type*} [DecidableEq V]

noncomputable def rateAt (p : Parameters) (i : ℕ) : ℝ := p.rate ⟨i%16,Nat.mod_lt _ (by decide)⟩

theorem rateAt_fin (p : Parameters) (i : Fin 16) : rateAt p i.val=p.rate i := by
  simp only [rateAt,Nat.mod_eq_of_lt i.isLt]

structure Inputs (p : Parameters) (G : SimpleGraph V) (S I : Finset V)
    (z m : ℝ) (k : ℕ) : Prop where
  subset : I⊆S
  independent : G.IsIndepSet (I:Set V)
  activity_pos : 0<z
  mean_eq : m=hardCoreAvailableMean G S I z
  start_le : p.start≤m
  rank_eq : hardCoreMean G S z=(k:ℝ)
  variance_center : hardCoreVariance G S z-(z/(1+z))*(1-z/(1+z))*m≤
    p.R*((z/(1+z))*(1-z/(1+z))*m)
  variance_available : hardCoreAvailableVariance G S I z≤p.D*m
  variance_min : p.vmin≤(z/(1+z))*(1-z/(1+z))
  variance_max : (z/(1+z))*(1-z/(1+z))≤p.vmax
  near : 9/40≤(z/(1+z))*(1-z/(1+z))
  asymmetry : |1-2*(z/(1+z))|≤p.eta
  tails : ∀i : Fin 16,hardCoreAvailableLowerTail G S I z (cut i.val*m)≤Real.exp (-p.rate i*m)

theorem scale_eq {v m : ℝ} (hv : 0<v) :
    scale v m=Real.sqrt (2*Real.pi)*v*Real.sqrt v*(m*Real.sqrt m) := by
  unfold scale
  rw [Real.sqrt_mul hv.le]
  ring

theorem scale_badPrice {q m alpha : ℝ} (hv : 0<q*(1-q)) (hm : 0<m) (ha : 0<alpha) :
    scale (q*(1-q)) m*badPrice q (alpha*m)=(Real.pi^3/8)*alpha^(-(3/2:ℝ)) := by
  have hs : Real.sqrt ((q*(1-q))*m)≠0 := (Real.sqrt_pos.mpr (mul_pos hv hm)).ne'
  have haS : Real.sqrt alpha≠0 := (Real.sqrt_pos.mpr ha).ne'
  have hp : Real.sqrt (2*Real.pi)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have he : alpha*m*(q*(1-q))=alpha*((q*(1-q))*m) := by ring
  unfold scale badPrice
  rw [he,Real.sqrt_mul ha.le,rpow_neg_three_halves ha]
  field_simp [hv.ne']
  exact div_self hv.ne'

theorem normalized_bad_le (p : Parameters) {q m : ℝ}
    (hv : 0<q*(1-q)) (hm : 0<m) (hvp : q*(1-q)≤p.vmax) :
    scale (q*(1-q)) m*(Real.exp (-rateAt p 0*m)+
      ∑i∈range 15,badPrice q (cut i*m)*Real.exp (-rateAt p (i+1)*m))≤bad p m := by
  have hV := hv.trans_le hvp
  have hscale : scale (q*(1-q)) m≤Real.sqrt (2*Real.pi)*p.vmax*Real.sqrt p.vmax*(m*Real.sqrt m) := by
    rw [scale_eq hv]
    gcongr
  have hsum : ∑i∈range 15,(scale (q*(1-q)) m*(badPrice q (cut i*m)*Real.exp (-rateAt p (i+1)*m)))=
      (Real.pi^3/8)*∑i : Fin 15,(cut i.val)^(-(3/2:ℝ))*Real.exp (-p.rate i.succ*m) := by
    simp_rw [←mul_assoc,scale_badPrice hv hm (cut_pos _)]
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum,←Fin.sum_univ_eq_sum_range]
    congr 1
  rw [mul_add,Finset.mul_sum,hsum]
  unfold bad powerExpCost
  rw [rpow_three_halves hm]
  apply add_le_add _ le_rfl
  simpa [rateAt,mul_assoc] using mul_le_mul_of_nonneg_right hscale (Real.exp_pos (-p.rate 0*m)).le

theorem actual_lower {p : Parameters} (hp : p.Valid) {G : SimpleGraph V} {S I : Finset V}
    {z m : ℝ} {k : ℕ} (h : Inputs p G S I z m k) (hk : 1≤k) :
    budget p m≤scale ((z/(1+z))*(1-z/(1+z))) m*
      tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  have hm0:=hp.start_pos.trans_le h.start_le
  have hm6 : 6≤m := hp.start_large.trans h.start_le
  have hv:=hp.vmin_pos.trans_le h.variance_min
  have hscale : 0<scale ((z/(1+z))*(1-z/(1+z))) m := by unfold scale; positivity
  have htail (i : ℕ) (hi : i≤15) :
      hardCoreAvailableLowerTail G S I z (cut i*m)≤Real.exp (-rateAt p i*m) := by
    simpa only [rateAt,Nat.mod_eq_of_lt (show i<16 by omega)] using h.tails ⟨i,by omega⟩
  have hraw:=CurvatureErrorLayerBudget.actual_curvature_lower G S I h.subset h.independent
    h.activity_pos h.mean_eq hm0 (by norm_num : (0:ℝ)<1/3) (by norm_num : (1/3:ℝ)<1)
    (by linarith : 2≤(1/3:ℝ)*m) hv le_rfl h.near h.asymmetry h.variance_available k hk
    (fun i=>cut i*m) (fun i=>Real.exp (-rateAt p i*m)) 14
    (mul_pos (cut_pos 0) hm0) (by norm_num [cut])
    (by intro i _; unfold cut; push_cast; nlinarith) htail
  have hmain:=SignedGaussianLayerBudget.actual_scaled_curvature_lower G S I h.subset h.independent
    h.activity_pos h.mean_eq hm0 h.rank_eq hv h.variance_center h.variance_available
  have herror:=normalizedError_le_central (by linarith : 3<m) hp.vmin_pos h.variance_min
    h.variance_max hp.eta_nonneg hp.D_nonneg
  rw [centralError_eq p hm0] at herror
  have hbad:=normalized_bad_le p hv hm0 h.variance_max
  have hmul:=mul_le_mul_of_nonneg_left hraw hscale.le
  rw [mul_sub,mul_sub,scale_averagedError hv hm0] at hmul
  have hcut : (1/3:ℝ)*m=m/3 := by ring
  simp only [hcut] at hmul
  have hswap (j M : ℕ) :
      GaussianCurvatureFourier.curvature ((M:ℝ)*((z/(1+z))*(1-z/(1+z))))
        ((k:ℝ)-binomialLayerMean j M z)=
      GaussianCurvatureFourier.curvature (((z/(1+z))*(1-z/(1+z)))*(M:ℝ))
        ((k:ℝ)-binomialLayerMean j M z) := by rw [mul_comm (M:ℝ)]
  simp_rw [hswap] at hmul
  change _≤scale ((z/(1+z))*(1-z/(1+z))) m*tiltedCenter (countIndependent G S) z (partitionFunction G S z) k at hmul
  change _≤scale ((z/(1+z))*(1-z/(1+z))) m*_ at hmain
  unfold CurvatureBudget.budget
  linarith

theorem actual_positive {p : Parameters} (hp : p.Valid) (hend : 0<budget p p.start)
    {G : SimpleGraph V} {S I : Finset V} {z m : ℝ} {k : ℕ}
    (h : Inputs p G S I z m k) (hk : 1≤k) :
    0<tiltedCenter (countIndependent G S) z (partitionFunction G S z) k := by
  have hb:=budget_positive hp hend h.start_le
  have hh:=hb.trans_le (actual_lower hp h hk)
  have hv:=hp.vmin_pos.trans_le h.variance_min
  have hm:=hp.start_pos.trans_le h.start_le
  exact pos_of_mul_pos_right hh (by unfold scale; positivity)

#print axioms actual_lower
#print axioms actual_positive
end ForestUnimodality.CurvatureBudgetGraph
