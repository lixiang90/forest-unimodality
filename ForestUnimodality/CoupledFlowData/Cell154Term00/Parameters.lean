import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell154Term00
open CoupledFlow


def environment : Environment := ⟨(1531/1395), (11/10), (26543193392324359504082108344560215059539/10000000000000000000000000000000000000000), (36543193392324359504082108344560215059539/10000000000000000000000000000000000000000), 9, (14357563944780876831639561027288882564817/10000000000000000000000000000000000000000), (4785418182328189935058371330835266257797/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (1531/2926)

def qb : ℚ := (11/21)

def rho : ℚ := (57335933199482923373424510557/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (49834869859636637506232445169/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell154Term00
