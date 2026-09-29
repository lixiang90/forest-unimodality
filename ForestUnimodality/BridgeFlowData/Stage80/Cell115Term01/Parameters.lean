import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell115Term01
open CoupledFlow


def environment : Environment := ⟨(11311/10425), (22647/20825), (13262151183695825992338963112679162474763/5000000000000000000000000000000000000000), (18262151183695825992338963112679162474763/5000000000000000000000000000000000000000), 9, (7174371799354037077986862549096010207361/5000000000000000000000000000000000000000), (19027555109365079648900464557087090199023/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (11311/21736)

def qb : ℚ := (22647/43472)

def rho : ℚ := (285265417215276195061863664943/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (271024780454505851812245857807/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell115Term01
