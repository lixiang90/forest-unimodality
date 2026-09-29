import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell063Term00
open CoupledFlow


def environment : Environment := ⟨(9287/9725), (24/25), (25735094849243505993884593334282341125257/10000000000000000000000000000000000000000), (35735094849243505993884593334282341125257/10000000000000000000000000000000000000000), 4, (12554825976888979654952626496941386902901/10000000000000000000000000000000000000000), (1750290359962947232353531102087298340829/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (9287/19012)

def qb : ℚ := (24/49)

def rho : ℚ := (10965039727666275883725687439/40000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (11678828403853685031638690021/125000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell063Term00
