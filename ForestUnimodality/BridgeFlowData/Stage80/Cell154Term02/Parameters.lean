import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell154Term02
open CoupledFlow


def environment : Environment := ⟨(23881/21275), (95549/85075), (26700503894922995590558681453638111236599/10000000000000000000000000000000000000000), (36700503894922995590558681453638111236599/10000000000000000000000000000000000000000), 10, (14869259878527959894177371302868209188419/10000000000000000000000000000000000000000), (19414343867127277137491648143179576858811/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (23881/45156)

def qb : ℚ := (95549/180624)

def rho : ℚ := (288276113952493223088760870051/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (279188737026414260437753839469/1000000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell154Term02
