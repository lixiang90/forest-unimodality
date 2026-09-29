import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell026Term01
open CoupledFlow


def environment : Environment := ⟨(4/5), (301/365), (26156156156156156156156156156156156156157/10000000000000000000000000000000000000000), (36156156156156156156156156156156156156157/10000000000000000000000000000000000000000), 2, (2913783677278674250029259623430207192019/2500000000000000000000000000000000000000), (4085211337463589715841968094220346472599/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (4/9)

def qb : ℚ := (301/666)

def rho : ℚ := (1/4)

def retention : ℚ := (1/1000)

def rate : ℚ := (58756240295580166900107851219/250000000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell026Term01
