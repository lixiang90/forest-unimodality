import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell221Term01
open CoupledFlow


def environment : Environment := ⟨(33/20), (467/275), (30142380644393295592816634944876006932777/10000000000000000000000000000000000000000), (40142380644393295592816634944876006932777/10000000000000000000000000000000000000000), 15, (3995911506051799136935580431864162504367/1250000000000000000000000000000000000000), (25264813693977990622433111211936786034511/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (33/53)

def qb : ℚ := (467/742)

def rho : ℚ := (313573855762967357095416050879/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (6831835002826743619220526363/62500000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell221Term01
