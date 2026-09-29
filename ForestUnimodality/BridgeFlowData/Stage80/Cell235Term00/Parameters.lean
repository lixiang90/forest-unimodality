import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell235Term00
open CoupledFlow


def environment : Environment := ⟨(107/49), (9/4), (8032385503269729930580570788596096035823/2500000000000000000000000000000000000000), (10532385503269729930580570788596096035823/2500000000000000000000000000000000000000), 15, (33811243846782454772627813035043127141689/10000000000000000000000000000000000000000), (29166606009054636730838503722266112099203/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (107/156)

def qb : ℚ := (9/13)

def rho : ℚ := (65731328585795555549927953377/200000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (149572838702056300286120170989/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell235Term00
