import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell146Term01
open CoupledFlow


def environment : Environment := ⟨(95749/84875), (47887/42425), (3388133391888763938230118508043826835657/1250000000000000000000000000000000000000), (4638133391888763938230118508043826835657/1250000000000000000000000000000000000000), 10, (7531916010029874293303919260503735191831/5000000000000000000000000000000000000000), (4918644116781318954513811785691707318609/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (95749/180624)

def qb : ℚ := (47887/90312)

def rho : ℚ := (142902211132667011809056134731/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (145608082773262908988024408153/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell146Term01
