import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell113Term03
open CoupledFlow


def environment : Environment := ⟨(2294/2095), (1531/1395), (6718651729587943945094660891442539281853/2500000000000000000000000000000000000000), (9218651729587943945094660891442539281853/2500000000000000000000000000000000000000), 9, (1814035152116300260163858580515171779481/1250000000000000000000000000000000000000), (9647133149691826507135971172111092030429/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (2294/4389)

def qb : ℚ := (1531/2926)

def rho : ℚ := (70948541788570732648746558673/250000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (137890692683947692317530088689/500000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell113Term03
