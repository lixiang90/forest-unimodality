import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell034Term01
open CoupledFlow


def environment : Environment := ⟨(1677/1895), (841/945), (25257156074717110816264924890222627937167/10000000000000000000000000000000000000000), (35257156074717110816264924890222627937167/10000000000000000000000000000000000000000), 3, (5893631295924240549574796244294478947767/5000000000000000000000000000000000000000), (16602053896325358452675700914152984375789/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (1677/3572)

def qb : ℚ := (841/1786)

def rho : ℚ := (133557186931568315609889186161/500000000000000000000000000000)

def retention : ℚ := (7/20)

def rate : ℚ := (230114895403830421240751643273/1000000000000000000000000000000)

def finish : ℚ := (104982212449867768832987083269936104601/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell034Term01
