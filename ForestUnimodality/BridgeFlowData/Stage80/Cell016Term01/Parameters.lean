import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell016Term01
open CoupledFlow


def environment : Environment := ⟨(19/32), (97/158), (10215686274509803921568627450980392156863/5000000000000000000000000000000000000000), (15215686274509803921568627450980392156863/5000000000000000000000000000000000000000), 1, (8278423226976979192920500510001871773537/10000000000000000000000000000000000000000), (2893963860053825451749327181853133410227/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (19/51)

def qb : ℚ := (97/255)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (8437532995077606726496795911/40000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell016Term01
