import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell144Term00
open CoupledFlow


def environment : Environment := ⟨(95699/84925), (7977/7075), (846730713151625615133400903320678482269/312500000000000000000000000000000000000), (1159230713151625615133400903320678482269/312500000000000000000000000000000000000), 10, (7529587565777512677448510476464089327469/5000000000000000000000000000000000000000), (4914793196285154149305946853993649882041/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (95699/180624)

def qb : ℚ := (7977/15052)

def rho : ℚ := (35716223647102586306462333217/125000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50525450721353641398695231603/500000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell144Term00
