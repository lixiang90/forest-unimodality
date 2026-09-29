import ForestUnimodality.BasicFlowTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BasicFlowData.Cell013Term01
open BasicFlow


def qa : ℚ := (89/255)

def qb : ℚ := (91/255)

def rho : ℚ := (1/4)

def b : ℚ := (91/164)

def beta : ℚ := (18549019607843137254901960784313725490197/10000000000000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (6034266429043327582459846891/31250000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    qb/(1-qb)≤b ∧ 2*qb/rho-1≤beta := by decide +kernel

#print axioms normalization_checked

end ForestUnimodality.BasicFlowData.Cell013Term01
