import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell136Term02
open CoupledFlow


def environment : Environment := ⟨(31833/28375), (23881/21275), (21645296204010132630691029028400619543/8000000000000000000000000000000000000), (29645296204010132630691029028400619543/8000000000000000000000000000000000000), 10, (15040535057072559973181205391232808325693/10000000000000000000000000000000000000000), (979879914418856266821591350301226851507/500000000000000000000000000000000000000)⟩

def qa : ℚ := (31833/60208)

def qb : ℚ := (23881/45156)

def rho : ℚ := (285431061675961532961728979009/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (54615231908029216706970842541/200000000000000000000000000000)

def finish : ℚ := (9151744581635071/5000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell136Term02
