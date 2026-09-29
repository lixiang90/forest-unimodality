import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell181Term00
open CoupledFlow


def environment : Environment := ⟨(9/5), (41/22), (6270971283081704601909682530237839037249/2000000000000000000000000000000000000000), (8270971283081704601909682530237839037249/2000000000000000000000000000000000000000), 15, (3309262196820450571023847245614417366839/1000000000000000000000000000000000000000), (26913477984630943545896586011091380994223/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/14)

def qb : ℚ := (41/63)

def rho : ℚ := (157368132114024157314190088539/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (42667396600759754979285784631/250000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell181Term00
