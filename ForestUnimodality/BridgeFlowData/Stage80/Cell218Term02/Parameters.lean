import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell218Term02
open CoupledFlow


def environment : Environment := ⟨(53/37), (107/73), (14520087826073610007341405582035228085279/5000000000000000000000000000000000000000), (19520087826073610007341405582035228085279/5000000000000000000000000000000000000000), 14, (5084314984906074769189585484083456794111/2500000000000000000000000000000000000000), (2320721552655418078650589330308632672361/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/90)

def qb : ℚ := (107/180)

def rho : ℚ := (76132398806426712676413099619/250000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (52549800948197174654828116649/250000000000000000000000000000)

def finish : ℚ := (3218875824868200749201518666452375279/2000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell218Term02
