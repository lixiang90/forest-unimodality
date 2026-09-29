import ForestUnimodality.LowActivityFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.LowActivityFlowData.Cell004
open LowActivityFlow


def qa : ℚ := (39/140)

def qb : ℚ := (2/7)

def rho : ℚ := (1/4)

def b : ℚ := (2/5)

def beta : ℚ := (6428571428571428571428571428571428571429/5000000000000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (178771866626511003317442828407/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    qb/(1-qb)≤b ∧ 2*qb/rho-1≤beta := by decide +kernel

#print axioms normalization_checked

end ForestUnimodality.LowActivityFlowData.Cell004
