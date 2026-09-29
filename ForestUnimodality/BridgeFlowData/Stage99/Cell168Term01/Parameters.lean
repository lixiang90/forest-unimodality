import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell168Term01
open CoupledFlow


def environment : Environment := ⟨(107/80), (27/20), (14346627591616134683014860108950361429133/5000000000000000000000000000000000000000), (19346627591616134683014860108950361429133/5000000000000000000000000000000000000000), 14, (20125398233218342569468186774203221780879/10000000000000000000000000000000000000000), (889121608465762785432172294368782567807/400000000000000000000000000000000000000)⟩

def qa : ℚ := (107/187)

def qb : ℚ := (27/47)

def rho : ℚ := (148467241224855346263580965041/500000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (96606344672019184571179495039/500000000000000000000000000000)

def finish : ℚ := (3218875824868200749201518666452375279/2000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell168Term01
