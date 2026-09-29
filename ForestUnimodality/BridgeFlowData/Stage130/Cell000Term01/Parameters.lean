import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell000Term01
open CoupledFlow


def environment : Environment := ⟨(1/3), (9/26), (2642857142857142857142857142857142857143/2500000000000000000000000000000000000000), (5142857142857142857142857142857142857143/2500000000000000000000000000000000000000), 0, (396690085171622845987753436730578222917/1000000000000000000000000000000000000000), (2644897959183673469387755102040816326531/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1/4)

def qb : ℚ := (9/35)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (166932450078174175680359616621/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell000Term01
