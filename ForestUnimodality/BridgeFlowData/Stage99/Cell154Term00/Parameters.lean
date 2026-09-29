import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell154Term00
open CoupledFlow


def environment : Environment := ⟨(48539/42625), (97103/85225), (3398319948116014498765440860834445117651/1250000000000000000000000000000000000000), (4648319948116014498765440860834445117651/1250000000000000000000000000000000000000), 10, (15103017849650947300550335280883393627369/10000000000000000000000000000000000000000), (3960912745574212240565316167869835674251/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (48539/91164)

def qb : ℚ := (97103/182328)

def rho : ℚ := (286433147239373449663066062013/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (4067160861625607026785774341/40000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell154Term00
