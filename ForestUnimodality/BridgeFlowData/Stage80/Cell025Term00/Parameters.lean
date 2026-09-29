import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell025Term00
open CoupledFlow


def environment : Environment := ⟨(67/86), (4/5), (24876523983175571145437000530291776510947/10000000000000000000000000000000000000000), (34876523983175571145437000530291776510947/10000000000000000000000000000000000000000), 2, (5581753574945271523903126751891043546161/5000000000000000000000000000000000000000), (7750338662927904698986000117842617002433/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (67/153)

def qb : ℚ := (4/9)

def rho : ℚ := (50973479428035243875917433551/200000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (150106131172842912568870679403/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell025Term00
