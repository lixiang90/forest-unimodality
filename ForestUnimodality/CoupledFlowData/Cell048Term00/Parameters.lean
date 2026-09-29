import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell048Term00
open CoupledFlow


def environment : Environment := ⟨(2983/3225), (4487/4825), (25535081644725221768997098727159072179791/10000000000000000000000000000000000000000), (35535081644725221768997098727159072179791/10000000000000000000000000000000000000000), 4, (12470895076502400970553902637738229380757/10000000000000000000000000000000000000000), (2140328491997987409760121107022695941671/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (2983/6208)

def qb : ℚ := (4487/9312)

def rho : ℚ := (135598780773301553703491654279/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (9139661641666458664556103613/100000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell048Term00
