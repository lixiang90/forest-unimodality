import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell048Term01
open CoupledFlow


def environment : Environment := ⟨(9237/9775), (4631/4875), (26515038305760080630447486303233490232093/10000000000000000000000000000000000000000), (36515038305760080630447486303233490232093/10000000000000000000000000000000000000000), 4, (402561624995313905882615894782077179389/312500000000000000000000000000000000000), (17788885166628964169956060285111960158303/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9237/19012)

def qb : ℚ := (4631/9506)

def rho : ℚ := (133415168934367147688556041087/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (33842573802848850666783157323/200000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell048Term01
