import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell184Term01
open CoupledFlow


def environment : Environment := ⟨(47887/42425), (31933/28275), (26682839268704830327968859909283860428831/10000000000000000000000000000000000000000), (36682839268704830327968859909283860428831/10000000000000000000000000000000000000000), 10, (594430510480154545405567096549831483109/400000000000000000000000000000000000000), (9727885882005309484312961761586180533101/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (47887/90312)

def qb : ℚ := (31933/60208)

def rho : ℚ := (36146194884823588849287094977/125000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20231355979958750175018034849/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell184Term01
