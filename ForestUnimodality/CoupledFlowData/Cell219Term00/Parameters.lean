import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell219Term00
open CoupledFlow


def environment : Environment := ⟨(63/40), (129/80), (29719241503560357144611787558781927424409/10000000000000000000000000000000000000000), (39719241503560357144611787558781927424409/10000000000000000000000000000000000000000), 15, (3946797624828512795846718395598049870779/1250000000000000000000000000000000000000), (12257852042964799214485455969097771860643/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (63/103)

def qb : ℚ := (129/209)

def rho : ℚ := (155396945414339862741725717889/500000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (2988298433148563212873644183/100000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell219Term00
