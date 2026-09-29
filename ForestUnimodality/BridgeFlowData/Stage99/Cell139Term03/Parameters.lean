import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell139Term03
open CoupledFlow


def environment : Environment := ⟨(15929/14175), (95599/85025), (2707116096694469759957927933993102488529/1000000000000000000000000000000000000000), (3707116096694469759957927933993102488529/1000000000000000000000000000000000000000), 10, (15047527434809087502275026922674282437069/10000000000000000000000000000000000000000), (19620681179017993986525486788123760120521/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (15929/30104)

def qb : ℚ := (95599/180624)

def rho : ℚ := (28554312111229889889460099571/100000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (138284838713136757212141927327/500000000000000000000000000000)

def finish : ℚ := (2288773858445983/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell139Term03
