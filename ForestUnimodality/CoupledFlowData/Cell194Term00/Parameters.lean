import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell194Term00
open CoupledFlow


def environment : Environment := ⟨(29/25), (2557/2195), (3369249012403509974960791838872979428029/1250000000000000000000000000000000000000), (4619249012403509974960791838872979428029/1250000000000000000000000000000000000000), 12, (15622388298665217918073228234230769604537/10000000000000000000000000000000000000000), (9942272495551999163278404656564148482719/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (29/54)

def qb : ℚ := (2557/4752)

def rho : ℚ := (72805290446612608885452186769/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (49465896368767294135323398961/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell194Term00
