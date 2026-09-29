import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell201Term03
open CoupledFlow


def environment : Environment := ⟨(116/91), (13/10), (3506624603516027137176868546104989368469/1250000000000000000000000000000000000000), (4756624603516027137176868546104989368469/1250000000000000000000000000000000000000), 13, (17349165296490149370538501864638841273239/10000000000000000000000000000000000000000), (21508215598507253142017144730213864970469/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (116/207)

def qb : ℚ := (13/23)

def rho : ℚ := (297068529901722442523990052613/1000000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (2360382938427962952890918827/10000000000000000000000000000)

def finish : ℚ := (3218875824868200749201518666452375279/2000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell201Term03
