import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell007Term02
open CoupledFlow


def environment : Environment := ⟨(19/44), (13/29), (7380952380952380952380952380952380952381/5000000000000000000000000000000000000000), (12380952380952380952380952380952380952381/5000000000000000000000000000000000000000), 0, (2571493958604282234735800143087961690997/5000000000000000000000000000000000000000), (1916099773242630385487528344671201814059/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (19/63)

def qb : ℚ := (13/42)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (189784570266272526604206191171/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell007Term02
