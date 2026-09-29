import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell111Term00
open CoupledFlow


def environment : Environment := ⟨(4583/4195), (2294/2095), (26854552248160669276952207673782489057231/10000000000000000000000000000000000000000), (36854552248160669276952207673782489057231/10000000000000000000000000000000000000000), 9, (7251460025147903119591327937734463606879/5000000000000000000000000000000000000000), (19262780327473359608413844703498981521369/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (4583/8778)

def qb : ℚ := (2294/4389)

def rho : ℚ := (8863733926011841853476962351/31250000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (12416114731108444847279260909/125000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell111Term00
