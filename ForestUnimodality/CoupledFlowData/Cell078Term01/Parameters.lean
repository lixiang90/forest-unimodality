import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell078Term01
open CoupledFlow


def environment : Environment := ⟨(3193/3275), (49/50), (5172701651808897546873015722534643686123/2000000000000000000000000000000000000000), (7172701651808897546873015722534643686123/2000000000000000000000000000000000000000), 5, (2600925864571675860908417465162805186619/2000000000000000000000000000000000000000), (4437656324982777522686588010154009351263/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (3193/6468)

def qb : ℚ := (49/99)

def rho : ℚ := (17251153016544075690277703103/62500000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (10830399457270792529835235583/62500000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell078Term01
