import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell044Term00
open CoupledFlow


def environment : Environment := ⟨(2983/3225), (4487/4825), (2666480653714737243201349510526818515769/1000000000000000000000000000000000000000), (3666480653714737243201349510526818515769/1000000000000000000000000000000000000000), 4, (12944767620096618969874305082632486529619/10000000000000000000000000000000000000000), (17666987428283962639867327377291489132577/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2983/6208)

def qb : ℚ := (4487/9312)

def rho : ℚ := (32855169580824969518170146517/125000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (91393973228617884924039116213/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell044Term00
