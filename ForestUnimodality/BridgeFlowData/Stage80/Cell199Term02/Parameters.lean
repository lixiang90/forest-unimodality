import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02
open CoupledFlow


def environment : Environment := ⟨(99/80), (5/4), (27649011985309657614308668848108041177531/10000000000000000000000000000000000000000), (37649011985309657614308668848108041177531/10000000000000000000000000000000000000000), 13, (4283030133697717140667278727934584552779/2500000000000000000000000000000000000000), (10458058884808238226196852457807789215981/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (99/179)

def qb : ℚ := (5/9)

def rho : ℚ := (3689044720299226415455774407/12500000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (230133174594352125495792263697/1000000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell199Term02
