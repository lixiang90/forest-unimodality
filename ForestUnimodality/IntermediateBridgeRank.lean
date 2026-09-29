import ForestUnimodality.IntermediateBridgeCover
import ForestUnimodality.ActivityPointDensityTransfer

/-! Integer ranks for the actual hard-core mean. The numerical witness is
checked against an independently valid point-density certificate. -/
namespace ForestUnimodality.IntermediateBridgeCover
variable {ι : Type*}

def Band.RankValid (s : Band ι) : Prop :=
  ∀ {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (z : ℝ) (k : ℕ),
    G.IsAcyclic → s.lowerOrder≤S.card → 0<z →
    z/(1+z)∈Set.Icc (s.qlo:ℝ) (s.qhi:ℝ) →
    (S.card:ℝ)/4≤hardCoreMean G S z → hardCoreMean G S z=k → (s.rank:ℝ)≤k

theorem Band.rank_of_central (s : Band ι)
    (hc : 4*((s.rank:ℚ)-1)<s.lowerOrder) : s.RankValid := by
  intro V _ G S z k _ hn _ _ hrank hmean
  have hnR : (s.lowerOrder:ℝ)≤S.card := by exact_mod_cast hn
  have hcR : 4*((s.rank:ℝ)-1)<s.lowerOrder := by exact_mod_cast hc
  rw [hmean] at hrank
  by_contra h
  have hlt : k<s.rank := by exact_mod_cast (lt_of_not_ge h)
  have hku : (k:ℝ)+1≤s.rank := by exact_mod_cast (show k+1≤s.rank by omega)
  linarith

def Band.rankCheck (s : Band ι) (c : ActivityPointDensity.Certificate) (gamma : ℚ) : Bool :=
  let a := s.qlo/(1-s.qlo)
  decide (8≤s.lowerOrder ∧ s.qlo<1 ∧
    0<c.parameters.x ∧ c.parameters.x≤a ∧ 0≤gamma ∧
    gamma^2*c.parameters.x*(1+a)≤a*(1+c.parameters.x) ∧
    0≤c.parameters.r ∧ (s.rank:ℚ)-1<gamma*(c.parameters.r*s.lowerOrder+c.parameters.h))

theorem Band.rank_of_certificate (s : Band ι) (c : ActivityPointDensity.Certificate)
    (hc : c.Valid) (gamma : ℚ) (hcheck : s.rankCheck c gamma=true) : s.RankValid := by
  have ht : 8≤s.lowerOrder ∧ s.qlo<1 ∧
      0<c.parameters.x ∧ c.parameters.x≤s.qlo/(1-s.qlo) ∧ 0≤gamma ∧
      gamma^2*c.parameters.x*(1+s.qlo/(1-s.qlo))≤
        s.qlo/(1-s.qlo)*(1+c.parameters.x) ∧
      0≤c.parameters.r ∧ (s.rank:ℚ)-1<gamma*(c.parameters.r*s.lowerOrder+c.parameters.h) := by
    simpa only [rankCheck,decide_eq_true_eq] using hcheck
  rcases ht with ⟨h8,hq1,hx,hxa,hg,hfactor,hr,hthreshold⟩
  intro V _ G S z k hG hn hz hq _ hmean
  have hq1R : (s.qlo:ℝ)<1 := by exact_mod_cast hq1
  have haz : (s.qlo:ℝ)/(1-s.qlo)≤z := by
    apply (div_le_iff₀ (sub_pos.mpr hq1R)).mpr
    have hl := (le_div_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.1
    nlinarith
  have hd := ActivityPointDensity.Certificate.transferred_density hc G hG S (h8.trans hn)
    (a:=(s.qlo:ℝ)/(1-s.qlo)) (gamma:=(gamma:ℝ))
    (by exact_mod_cast hx) (by exact_mod_cast hxa) haz
    (by exact_mod_cast hg) (by exact_mod_cast hfactor)
  have hnR : (s.lowerOrder:ℝ)≤S.card := by exact_mod_cast hn
  have hrR : (0:ℝ)≤c.parameters.r := by exact_mod_cast hr
  have hgR : (0:ℝ)≤gamma := by exact_mod_cast hg
  have hmono := mul_le_mul_of_nonneg_left (add_le_add_right
    (mul_le_mul_of_nonneg_left hnR hrR) (c.parameters.h:ℝ)) hgR
  have hthresholdR : (s.rank:ℝ)-1<(gamma:ℝ)*
      ((c.parameters.r:ℝ)*s.lowerOrder+c.parameters.h) := by exact_mod_cast hthreshold
  rw [hmean] at hd
  by_contra h
  have hlt : k<s.rank := by exact_mod_cast (lt_of_not_ge h)
  have hku : (k:ℝ)+1≤s.rank := by exact_mod_cast (show k+1≤s.rank by omega)
  linarith

#print axioms Band.rank_of_central
#print axioms Band.rank_of_certificate
end ForestUnimodality.IntermediateBridgeCover
