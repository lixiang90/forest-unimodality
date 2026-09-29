import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell049Term01
open CoupledFlow


def environment : Environment := ⟨(9237/9775), (4631/4875), (28764252023720801070494035456001722219119/10000000000000000000000000000000000000000), (38764252023720801070494035456001722219119/10000000000000000000000000000000000000000), 4, (13824282115335240739685216692271987547077/10000000000000000000000000000000000000000), (18884625617699456107454016220991371301993/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9237/19012)

def qb : ℚ := (4631/9506)

def rho : ℚ := (125674035996535671754898776659/500000000000000000000000000000)

def retention : ℚ := (1/1000)

def rate : ℚ := (7561718281040784954940090031/31250000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell049Term01
