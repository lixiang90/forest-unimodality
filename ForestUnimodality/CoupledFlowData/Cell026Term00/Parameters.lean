import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell026Term00
open CoupledFlow


def environment : Environment := ⟨(4/5), (301/365), (2507813418502478664723861556011947383841/1000000000000000000000000000000000000000), (3507813418502478664723861556011947383841/1000000000000000000000000000000000000000), 2, (702562687009350852448442266693922869169/625000000000000000000000000000000000000), (7926815607877222808422540002699670889911/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (4/9)

def qb : ℚ := (301/666)

def rho : ℚ := (128841502677441393413808809099/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (121562321085637518510750523287/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell026Term00
