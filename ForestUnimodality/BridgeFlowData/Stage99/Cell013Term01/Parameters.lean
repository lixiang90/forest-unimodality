import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell013Term01
open CoupledFlow


def environment : Environment := ⟨(89/166), (91/164), (18549019607843137254901960784313725490197/10000000000000000000000000000000000000000), (28549019607843137254901960784313725490197/10000000000000000000000000000000000000000), 1, (3820007078221509987471828560889366120419/5000000000000000000000000000000000000000), (2547020376778162245290272971933871587851/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (89/255)

def qb : ℚ := (91/255)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (40094942478051003366597622083/200000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell013Term01
