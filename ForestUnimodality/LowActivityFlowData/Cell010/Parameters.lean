import ForestUnimodality.LowActivityFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.LowActivityFlowData.Cell010
open LowActivityFlow


def qa : ℚ := (41/126)

def qb : ℚ := (1/3)

def rho : ℚ := (1/4)

def b : ℚ := (1/2)

def beta : ℚ := (16666666666666666666666666666666666666667/10000000000000000000000000000000000000000)

def retention : ℚ := (1/1000)

def rate : ℚ := (12549398151803045997099287937/62500000000000000000000000000)

def finish : ℚ := (345387763949106852602698718202654631139/50000000000000000000000000000000000000)

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    qb/(1-qb)≤b ∧ 2*qb/rho-1≤beta := by decide +kernel

#print axioms normalization_checked

end ForestUnimodality.LowActivityFlowData.Cell010
