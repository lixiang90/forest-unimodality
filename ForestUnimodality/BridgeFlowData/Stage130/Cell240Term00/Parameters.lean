import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell240Term00
open CoupledFlow


def environment : Environment := ⟨(35/17), (53/25), (32377650469904786797473892506241437974817/10000000000000000000000000000000000000000), (42377650469904786797473892506241437974817/10000000000000000000000000000000000000000), 15, (34041337381428981076508058614867967617629/10000000000000000000000000000000000000000), (28795070191089150003411747472189695034171/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (35/52)

def qb : ℚ := (53/78)

def rho : ℚ := (64136371125126809749987892843/200000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (1212818922395377816663534069/10000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell240Term00
