import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell029Term02
open CoupledFlow


def environment : Environment := ⟨(1613/1865), (22/25), (5074972728701077055780419103531535648821/2000000000000000000000000000000000000000), (7074972728701077055780419103531535648821/2000000000000000000000000000000000000000), 3, (5917201324548098758999362751154245250167/5000000000000000000000000000000000000000), (8279223405926792299317511716898605546493/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1613/3478)

def qb : ℚ := (22/47)

def rho : ℚ := (264642776351120362246465169527/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (33186931595920477850666983507/125000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell029Term02
