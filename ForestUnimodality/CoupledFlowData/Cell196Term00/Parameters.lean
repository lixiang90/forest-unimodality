import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell196Term00
open CoupledFlow


def environment : Environment := ⟨(427/365), (2567/2185), (27026040734166160107898387096205233687539/10000000000000000000000000000000000000000), (37026040734166160107898387096205233687539/10000000000000000000000000000000000000000), 12, (15658496145326755191477830334733184101941/10000000000000000000000000000000000000000), (20001230337669304081855042019351606665807/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (427/792)

def qb : ℚ := (2567/4752)

def rho : ℚ := (291791178307181781819258158999/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (99703725840916111205238966653/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell196Term00
