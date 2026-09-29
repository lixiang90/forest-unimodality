import ForestUnimodality.CorrelatedTwoPhaseCertificate
import ForestUnimodality.Stage170SourceData.Windows.Batch040_059

namespace ForestUnimodality.CorrelatedTwoPhaseData.Stage130Cell220Term00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def qa : ℚ := (13/23)
def qb : ℚ := (21/37)
def rho : ℚ := (293866307348293569444703934861/1000000000000000000000000000000)
def b : ℚ := (21/16)
def u : ℚ := (32586997740370487/100000000000000000)
def v : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)
def retention : ℚ := (7/10)
def rate : ℚ := (16087301896897451019379552263/125000000000000000000000000000)
def A : ℚ := (197253/1250000)
def C₁ : ℚ := (8245781/5000000)
def C₂ : ℚ := (3719451599/1000000000)
def ulo : ℚ := (72189904451784375778327619223189232787140599220617/100000000000000000000000000000000000000000000000000)
def uhi : ℚ := (36094952225892187889163809611594616393570299610309/50000000000000000000000000000000000000000000000000)
def vlo : ℚ := (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000)
def vhi : ℚ := (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)
def expU : ExpEnclosure.PowerCertificate := ⟨1, (-32586997740370487/100000000000000000), 64, (72189904451784375778327619223189232787140599220617/100000000000000000000000000000000000000000000000000), (36094952225892187889163809611594616393570299610309/50000000000000000000000000000000000000000000000000)⟩
def expV : ExpEnclosure.PowerCertificate := ⟨1, (-17833747196936618945631935562059223897/50000000000000000000000000000000000000), 64, (70000000000000000000000000000000000001681173133283/100000000000000000000000000000000000000000000000000), (17500000000000000000000000000000000000420293283321/25000000000000000000000000000000000000000000000000)⟩
theorem expU_checked : expU.check (-u) ulo uhi=true := by decide +kernel
theorem expV_checked : expV.check (-v) vlo vhi=true := by decide +kernel
theorem coefficients_checked : A=(AffineSourceLibrary.parameters (13:Fin 15)).A ∧
    C₁=(AffineSourceLibrary.parameters (13:Fin 15)).C ∧
    C₂=(TiltedSourceLibrary.parameters (33:Fin 36)).C := by decide +kernel
def first_lo : FlowComparisonCertificate.Certificate := ⟨⟨1, (-268705246814589894665347/500000000000000000000000), 64, (58425923819547029043845315811458523778762453854377/100000000000000000000000000000000000000000000000000), (29212961909773514521922657905729261889381226927189/50000000000000000000000000000000000000000000000000)⟩, (58425923819547029043845315811458523778762453854377/100000000000000000000000000000000000000000000000000), (29212961909773514521922657905729261889381226927189/50000000000000000000000000000000000000000000000000), (1361988735352667958754441131905865806333/5000000000000000000000000000000000000000), (504186033808719525247574295127914217237/2000000000000000000000000000000000000000)⟩
def second_lo : FlowComparisonCertificate.Certificate := ⟨⟨1, (-5728879101792477876705040291766144056395661303/50000000000000000000000000000000000000000000000), 64, (89174275251617406858077547805167326664073307917329/100000000000000000000000000000000000000000000000000), (8917427525161740685807754780516732666407330791733/10000000000000000000000000000000000000000000000000)⟩, (89174275251617406858077547805167326664073307917329/100000000000000000000000000000000000000000000000000), (8917427525161740685807754780516732666407330791733/10000000000000000000000000000000000000000000000000), 0, (58211402730946482962540909756479793009/2000000000000000000000000000000000000000)⟩
theorem first_lo_checked : first_lo.check qa (A*(2*qa/rho-1)) C₁ u=true := by decide +kernel
theorem second_lo_checked : second_lo.check (first_lo.endBound qa) 0 C₂ (v-u)=true := by decide +kernel
theorem rate_lo_checked : rate≤first_lo.areaBound qa u+
    second_lo.areaBound (first_lo.endBound qa) (v-u) := by decide +kernel
theorem endpoint_lo : (rate:ℝ)≤CorrelatedTwoPhase.rate A C₁ C₂ rho u v qa :=
  CorrelatedTwoPhase.endpoint_sound first_lo second_lo
    first_lo_checked second_lo_checked rate_lo_checked
def first_hi : FlowComparisonCertificate.Certificate := ⟨⟨1, (-268705246814589894665347/500000000000000000000000), 64, (58425923819547029043845315811458523778762453854377/100000000000000000000000000000000000000000000000000), (29212961909773514521922657905729261889381226927189/50000000000000000000000000000000000000000000000000)⟩, (58425923819547029043845315811458523778762453854377/100000000000000000000000000000000000000000000000000), (29212961909773514521922657905729261889381226927189/50000000000000000000000000000000000000000000000000), (1369641219736811535658472672046686973849/5000000000000000000000000000000000000000), (504186033808719525247574295127914217237/2000000000000000000000000000000000000000)⟩
def second_hi : FlowComparisonCertificate.Certificate := ⟨⟨1, (-5728879101792477876705040291766144056395661303/50000000000000000000000000000000000000000000000), 64, (89174275251617406858077547805167326664073307917329/100000000000000000000000000000000000000000000000000), (8917427525161740685807754780516732666407330791733/10000000000000000000000000000000000000000000000000)⟩, (89174275251617406858077547805167326664073307917329/100000000000000000000000000000000000000000000000000), (8917427525161740685807754780516732666407330791733/10000000000000000000000000000000000000000000000000), 0, (58211402730946482962540909756479793009/2000000000000000000000000000000000000000)⟩
theorem first_hi_checked : first_hi.check qb (A*(2*qb/rho-1)) C₁ u=true := by decide +kernel
theorem second_hi_checked : second_hi.check (first_hi.endBound qb) 0 C₂ (v-u)=true := by decide +kernel
theorem rate_hi_checked : rate≤first_hi.areaBound qb u+
    second_hi.areaBound (first_hi.endBound qb) (v-u) := by decide +kernel
theorem endpoint_hi : (rate:ℝ)≤CorrelatedTwoPhase.rate A C₁ C₂ rho u v qb :=
  CorrelatedTwoPhase.endpoint_sound first_hi second_hi
    first_hi_checked second_hi_checked rate_hi_checked
variable {V : Type*} [DecidableEq V]
theorem actual_laplace {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hdensity : (rho:ℝ)*(S.card:ℝ)≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hzb : z≤(b:ℝ) := by
    have hq1 : (qb:ℝ)<1 := by norm_num [qb]
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<1+z)).mp hq.2
    have hzq : z≤(qb:ℝ)/(1-(qb:ℝ)) := (le_div_iff₀ (by linarith)).mpr (by nlinarith)
    exact hzq.trans (by norm_num [qb,b])
  have hρq : (rho:ℝ)≤z/(1+z) := (by norm_num [rho,qa] : (rho:ℝ)≤qa).trans hq.1
  have heU : Real.exp (-(u:ℝ))≤(uhi:ℝ) := by
    simpa only [Rat.cast_neg] using (expU.check_sound expU_checked).2
  have heV : (retention:ℝ)≤Real.exp (-(v:ℝ)) := by
    exact (by norm_num [retention,vlo] : (retention:ℝ)≤vlo).trans
      (by simpa only [Rat.cast_neg] using (expV.check_sound expV_checked).1)
  apply CorrelatedTwoPhase.actual_laplace (13:Fin 15) (33:Fin 36) (u := (u:ℝ)) hB hG hz
    (by norm_num [rho]) hρq hdensity (by norm_num [u]) (by norm_num [u,v])
    (by norm_num [retention]) heV
  · exact hzb.trans (by exact_mod_cast (show b≤(AffineSourceLibrary.domain (13:Fin 15)).b from by decide +kernel))
  · exact hzb.trans (by exact_mod_cast (show b≤(TiltedSourceLibrary.domain0 (33:Fin 36)).b from by decide +kernel))
  · exact (mul_le_mul hzb heU (Real.exp_pos _).le (by norm_num [b])).trans
      (by exact_mod_cast (show b*uhi≤(TiltedSourceLibrary.domain1 (33:Fin 36)).b from by decide +kernel))
  · exact hq
  · simpa only [coefficients_checked.1,coefficients_checked.2.1,coefficients_checked.2.2] using endpoint_lo
  · simpa only [coefficients_checked.1,coefficients_checked.2.1,coefficients_checked.2.2] using endpoint_hi
theorem actual_laplace_of_rank {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic) (hz : 0<z)
    (hq : z/(1+z)∈Set.Icc (qa:ℝ) (qb:ℝ))
    (hrank : (S.card:ℝ)/4≤hardCoreMean G S z) :
    hardCoreLayerLaplace G S B z retention≤Real.exp (-(rate:ℝ)*hardCoreAvailableMean G S B z) := by
  have hqw : z/(1+z)∈Set.Icc (Stage170SourceData.Window056.window.qa:ℝ)
      (Stage170SourceData.Window056.window.qb:ℝ) := hq
  have hr : rho=Stage170SourceData.Window056.window.rho := by decide +kernel
  apply actual_laplace hB hG hz hq
  simpa only [hr] using Stage170SourceData.Window056.window.density
    Stage170SourceData.Window056.valid G hG S hz hqw hrank

#print axioms actual_laplace_of_rank
#print axioms expU_checked
#print axioms expV_checked
#print axioms coefficients_checked
#print axioms endpoint_lo
#print axioms endpoint_hi
#print axioms actual_laplace
end ForestUnimodality.CorrelatedTwoPhaseData.Stage130Cell220Term00
