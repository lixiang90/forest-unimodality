import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell061Term00
open CoupledFlow


def environment : Environment := ⟨(4631/4875), (9287/9725), (25701890449750570711673115822001271548787/10000000000000000000000000000000000000000), (35701890449750570711673115822001271548787/10000000000000000000000000000000000000000), 4, (12540893556912028374749739355633287175497/10000000000000000000000000000000000000000), (3487938739815206713647256749830904785121/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (4631/9506)

def qb : ℚ := (9287/19012)

def rho : ℚ := (273644310281882930594772493241/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (46560078071670789376505151289/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell061Term00
