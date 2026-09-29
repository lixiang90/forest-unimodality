import ForestUnimodality.IntegerRankLogVariance

/-! Exact scalar certificates for logarithmic variance compression. A checked
certificate converts an explicit variance bound; it does not certify its source. -/
namespace ForestUnimodality.LogVarianceProfileCertificate

structure Certificate where
  qa : ℚ
  qb : ℚ
  a : ℚ
  lower : ℚ
  b : ℚ
  C : ℚ
  Cmu : ℚ
  D : ℚ
  ell : ℚ
  alpha : ℚ
  beta : ℚ
  nlo : ℚ
  nhi : ℚ
  rankUpper : ℚ
  logNLo : ℚ
  logNHi : ℚ
  logRootLo : ℚ
  logRootHi : ℚ
  logN : ElementaryEnclosure.LogCertificate
  logRoot : ElementaryEnclosure.LogCertificate
  deriving Repr

def Certificate.Accepts (c : Certificate) : Prop :=
  0<c.a ∧ 0<c.lower ∧ 0<1+c.b ∧ 0≤c.ell ∧ 0≤c.Cmu ∧
  c.logN.check (c.a/c.lower) c.logNLo c.logNHi=true ∧
  c.logRoot.check (1+c.a/(1+c.b)) c.logRootLo c.logRootHi=true ∧
  c.C*c.qa-c.qa*(1-c.qa)≤c.alpha ∧
  c.C*c.qb-c.qb*(1-c.qb)≤c.alpha ∧
  (c.D-c.ell*c.logNLo)*c.nlo-c.ell*c.logRootLo+c.Cmu*c.rankUpper≤c.beta ∧
  (c.D-c.ell*c.logNLo)*c.nhi-c.ell*c.logRootLo+c.Cmu*c.rankUpper≤c.beta

instance (c : Certificate) : Decidable c.Accepts := by
  unfold Certificate.Accepts
  infer_instance

def Certificate.check (c : Certificate) : Bool := decide c.Accepts

theorem Certificate.check_sound (c : Certificate) (hc : c.check=true)
    {z q n m k variance : ℝ} (haz : (c.a:ℝ)≤z) (hn : 0≤n)
    (hnlo : (c.nlo:ℝ)≤n) (hnhi : n≤(c.nhi:ℝ)) (hm : 0≤m)
    (hk : k≤(c.rankUpper:ℝ)) (hq : q∈Set.Icc (c.qa:ℝ) (c.qb:ℝ))
    (hvariance : variance≤(c.C:ℝ)*(q*m)+(c.Cmu:ℝ)*k+
      ((c.D:ℝ)-(c.ell:ℝ)*Real.log (z/c.lower))*n-
      (c.ell:ℝ)*Real.log (1+z/(1+c.b))) :
    variance≤(q*(1-q)+(c.alpha:ℝ))*m+c.beta := by
  have h : c.Accepts := of_decide_eq_true hc
  rcases h with ⟨ha,hl,hb,he,hcm,hln,hlr,hqa,hqb,hnl,hnh⟩
  have hlogn := (c.logN.check_sound hln).1
  have hlogroot := (c.logRoot.check_sound hlr).1
  apply log_variance_profile_of_rank_bound
    (g:=(c.D:ℝ)-(c.ell:ℝ)*c.logNLo) (root:=(c.ell:ℝ)*c.logRootLo)
    (by exact_mod_cast ha) (by exact_mod_cast hl) (by exact_mod_cast hb) haz
    (by exact_mod_cast he) hn hnlo hnhi hm (by exact_mod_cast hcm) hk hq
    (by exact_mod_cast hqa) (by exact_mod_cast hqb)
    (by simpa only [Rat.cast_div] using hlogn)
    (by simpa only [Rat.cast_add,Rat.cast_one,Rat.cast_div] using hlogroot)
    (le_refl _) (le_refl _) (by exact_mod_cast hnl) (by exact_mod_cast hnh) hvariance

#print axioms Certificate.check_sound
end ForestUnimodality.LogVarianceProfileCertificate
