import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell152Term03
open CoupledFlow


def environment : Environment := ⟨(24257/21325), (32351/28425), (27176986819698033194428534037699852877133/10000000000000000000000000000000000000000), (37176986819698033194428534037699852877133/10000000000000000000000000000000000000000), 10, (7549207445642499389813229427610006886827/5000000000000000000000000000000000000000), (3957854089127455152931938609495945572029/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (24257/45582)

def qb : ℚ := (32351/60776)

def rho : ℚ := (3579492175974425581396163541/12500000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (279712069232736505727486196189/1000000000000000000000000000000)

def finish : ℚ := (719041475725397/312500000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell152Term03
