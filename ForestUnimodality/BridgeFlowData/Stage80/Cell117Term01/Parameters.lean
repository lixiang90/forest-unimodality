import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell117Term01
open CoupledFlow


def environment : Environment := ⟨(22647/20825), (109/100), (13269190828906757698698244809743859308807/5000000000000000000000000000000000000000), (18269190828906757698698244809743859308807/5000000000000000000000000000000000000000), 9, (897207332915096484667195393958129084421/625000000000000000000000000000000000000), (19055902395701785542182858222603642724019/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (22647/43472)

def qb : ℚ := (109/209)

def rho : ℚ := (71367569773980750247702571681/250000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (271304297589629302995018841789/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell117Term01
