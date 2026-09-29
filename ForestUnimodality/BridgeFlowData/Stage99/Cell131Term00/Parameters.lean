import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell131Term00
open CoupledFlow


def environment : Environment := ⟨(47239/42225), (94503/84425), (27032373071822160055591641654656491039721/10000000000000000000000000000000000000000), (37032373071822160055591641654656491039721/10000000000000000000000000000000000000000), 10, (469652338395772663106526434211122409713/312500000000000000000000000000000000000), (1955909836585894656919865482926094503223/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (47239/89464)

def qb : ℚ := (94503/178928)

def rho : ℚ := (71310872349851254522598865723/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100590874040774888769851699807/1000000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell131Term00
