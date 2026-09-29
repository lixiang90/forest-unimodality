import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell019Term03
open CoupledFlow


def environment : Environment := ⟨(101/154), (103/152), (4462745098039215686274509803921568627451/2000000000000000000000000000000000000000), (6462745098039215686274509803921568627451/2000000000000000000000000000000000000000), 1, (2228730985439794767836984502352426338077/2500000000000000000000000000000000000000), (6526105344098423683198769703960015378701/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (101/255)

def qb : ℚ := (103/255)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (111316912928966484736270132977/500000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell019Term03
