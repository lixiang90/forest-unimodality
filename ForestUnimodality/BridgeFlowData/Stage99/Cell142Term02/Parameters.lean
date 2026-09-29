import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell142Term02
open CoupledFlow


def environment : Environment := ⟨(31883/28325), (47837/42475), (27085695977696697868910995293594356549917/10000000000000000000000000000000000000000), (37085695977696697868910995293594356549917/10000000000000000000000000000000000000000), 10, (15054516992017684839876490577748183128879/10000000000000000000000000000000000000000), (19643773125222306403967305362074510965081/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (31883/60208)

def qb : ℚ := (47837/90312)

def rho : ℚ := (35706892073616071230351288581/125000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (856194828583426789179231321/3125000000000000000000000000)

def finish : ℚ := (3667364316359827/2000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell142Term02
