import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell041Term01
open CoupledFlow


def environment : Environment := ⟨(2983/3225), (4487/4825), (713702749140893470790378006872852233677/250000000000000000000000000000000000000), (963702749140893470790378006872852233677/250000000000000000000000000000000000000), 4, (13733795179691949706883189982820348345557/10000000000000000000000000000000000000000), (18574459774034317025070558921127525655107/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2983/6208)

def qb : ℚ := (4487/9312)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (243765134821172999297759885481/1000000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell041Term01
