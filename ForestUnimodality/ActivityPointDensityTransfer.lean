import ForestUnimodality.ActivityPointDensityForest
import ForestUnimodality.HardCoreActivityGrowth
import ForestUnimodality.MeanMatchedSourceBudget

/-! Actual activity transfer and integer-rank rounding for point densities.
Only the integer target rank is rounded; the available-set mean stays real. -/
namespace ForestUnimodality.ActivityPointDensity
open Finset
variable {V : Type*} [DecidableEq V]

theorem mean_scaled_growth (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V)
    {x a gamma : ℝ} (hx : 0<x) (ha : x≤a) (hg : 0≤gamma)
    (hfactor : gamma^2*x*(1+a)≤a*(1+x)) :
    gamma*hardCoreMean G S x≤hardCoreMean G S a := by
  have ha0:=hx.trans_le ha
  have hgrowth:=hardCoreMean_sq_growth_of_isBipartite G hG.isBipartite S hx ha
  have hmul:=mul_le_mul_of_nonneg_right hfactor (sq_nonneg (hardCoreMean G S x))
  have hs : (gamma*hardCoreMean G S x)^2≤hardCoreMean G S a^2 := by
    apply (mul_le_mul_iff_right₀ (show 0<x*(1+a) by positivity)).mp
    nlinarith
  exact (sq_le_sq₀ (mul_nonneg hg (hardCoreMean_nonneg G S hx.le))
    (hardCoreMean_nonneg G S ha0.le)).mp hs

theorem Certificate.transferred_density {c : Certificate} (hc : c.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card)
    {a z gamma : ℝ} (hx : 0<(c.parameters.x:ℝ)) (hxa : (c.parameters.x:ℝ)≤a)
    (haz : a≤z) (hg : 0≤gamma)
    (hfactor : gamma^2*c.parameters.x*(1+a)≤a*(1+c.parameters.x)) :
    gamma*((c.parameters.r:ℝ)*S.card+c.parameters.h)≤hardCoreMean G S z := by
  have hpoint:=Certificate.forest_density hc G hG S hn
  have hgrowth:=mean_scaled_growth G hG S hx hxa hg hfactor
  have hm:= (hardCoreMean_strictMonoOn G S (card_pos.mp (by omega))).monotoneOn
    (hx.trans_le hxa) ((hx.trans_le hxa).trans_le haz) haz
  exact (mul_le_mul_of_nonneg_left hpoint hg).trans (hgrowth.trans hm)

/-- For a finite vertex window `n ≤ N`, a nonnegative intercept gives a
uniform density after division by the upper order, not the lower order. -/
theorem Certificate.finite_window_density {c : Certificate} (hc : c.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card)
    {N : ℕ} (hnN : S.card≤N) {a z gamma rho : ℝ}
    (hx : 0<(c.parameters.x:ℝ)) (hxa : (c.parameters.x:ℝ)≤a)
    (haz : a≤z) (hg : 0≤gamma)
    (hfactor : gamma^2*c.parameters.x*(1+a)≤a*(1+c.parameters.x))
    (hh : 0≤c.parameters.h)
    (hrho : rho≤gamma*(c.parameters.r+c.parameters.h/(N:ℝ))) :
    rho*S.card≤hardCoreMean G S z := by
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hnN' : (S.card:ℝ)≤N := by exact_mod_cast hnN
  have hh' : (0:ℝ)≤c.parameters.h := by exact_mod_cast hh
  have hb : (c.parameters.h:ℝ)/(N:ℝ)*S.card≤c.parameters.h := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN).mpr (mul_le_mul_of_nonneg_left hnN' hh')
  have h1:=mul_le_mul_of_nonneg_right hrho (show (0:ℝ)≤S.card by positivity)
  have h2:=mul_le_mul_of_nonneg_left hb hg
  have ht:=Certificate.transferred_density hc G hG S hn hx hxa haz hg hfactor
  nlinarith

/-- Only the target rank, already known to be an integer, is rounded. -/
theorem Certificate.rank_ceiling {c : Certificate} (hc : c.Valid)
    (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card)
    {N : ℕ} (hN : N≤S.card) {a z gamma : ℝ} {k : ℕ}
    (hx : 0<(c.parameters.x:ℝ)) (hxa : (c.parameters.x:ℝ)≤a)
    (haz : a≤z) (hg : 0≤gamma)
    (hfactor : gamma^2*c.parameters.x*(1+a)≤a*(1+c.parameters.x))
    (hk : hardCoreMean G S z=(k:ℝ)) :
    Nat.ceil (gamma*((c.parameters.r:ℝ)*N+c.parameters.h))≤k := by
  apply Nat.ceil_le.mpr
  have hr : (0:ℝ)≤c.parameters.r := by exact_mod_cast hc.2.2.2.2.2.2.1.2.1
  have hN' : (N:ℝ)≤S.card := by exact_mod_cast hN
  have hmono := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hN' hr) (le_refl (c.parameters.h:ℝ))) hg
  exact hmono.trans (hk ▸ Certificate.transferred_density hc G hG S hn hx hxa haz hg hfactor)

theorem available_lower_of_rank (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S B : Finset V) {z qb : ℝ} (hz : 0<z)
    (hB : IsMaximumMarginalIndependentOn G S B z)
    (hqb : z/(1+z)≤qb) {k kmin : ℕ}
    (hk : hardCoreMean G S z=(k:ℝ)) (hmin : kmin≤k) :
    (kmin:ℝ)/(2*qb)≤hardCoreAvailableMean G S B z := by
  have hq : 0<z/(1+z) := by positivity
  have hqb0:=hq.trans_le hqb
  have hm:=hardCoreAvailableMean_nonneg G S B hz.le
  have hhalf:=hB.half_mean hG.isBipartite
  have hmass:=hardCoreOccupiedMass_eq_activity_available_mean G S B hB.subset hB.independent hz
  have hmin' : (kmin:ℝ)≤k := by exact_mod_cast hmin
  apply (div_le_iff₀ (by positivity : 0<2*qb)).mpr
  rw [hmass,hk] at hhalf
  nlinarith [mul_nonneg (sub_nonneg.mpr hqb) hm]

#print axioms mean_scaled_growth
#print axioms Certificate.transferred_density
#print axioms Certificate.finite_window_density
#print axioms Certificate.rank_ceiling
#print axioms available_lower_of_rank
end ForestUnimodality.ActivityPointDensity
