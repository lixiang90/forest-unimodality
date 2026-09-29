import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell036Term01
open CoupledFlow


def environment : Environment := ⟨(1687/1885), (9/10), (5075000451285932115160535333041257987913/2000000000000000000000000000000000000000), (7075000451285932115160535333041257987913/2000000000000000000000000000000000000000), 3, (1183445815841336439431553039292165013487/1000000000000000000000000000000000000000), (8378290008101761715321686578601489722529/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1687/3572)

def qb : ℚ := (9/19)

def rho : ℚ := (53561462084737567380540586683/200000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (134879356915137387232269822421/500000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell036Term01
