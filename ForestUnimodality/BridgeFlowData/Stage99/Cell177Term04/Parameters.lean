import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell177Term04
open CoupledFlow


def environment : Environment := ⟨(129/80), (33/20), (6075823165931430034348519477775974694473/2000000000000000000000000000000000000000), (8075823165931430034348519477775974694473/2000000000000000000000000000000000000000), 15, (643741450846290345351021286568826740553/200000000000000000000000000000000000000), (25141713629786527465424636110057279709209/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (129/209)

def qb : ℚ := (33/53)

def rho : ℚ := (154198896295954128290826987897/500000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (205144011453784393748220956951/1000000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell177Term04
