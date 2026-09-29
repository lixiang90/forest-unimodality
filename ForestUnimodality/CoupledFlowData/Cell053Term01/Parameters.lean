import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell053Term01
open CoupledFlow


def environment : Environment := ⟨(8999/9625), (47/50), (25603308586848188268294695255077687880497/10000000000000000000000000000000000000000), (35603308586848188268294695255077687880497/10000000000000000000000000000000000000000), 4, (12499526616779384266999049635772749158753/10000000000000000000000000000000000000000), (1725108766579242111968918223699640546787/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (8999/18624)

def qb : ℚ := (47/97)

def rho : ℚ := (136092992956619134621855462741/500000000000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (13899345893463332539628658993/62500000000000000000000000000)

def finish : ℚ := (91629073187415506518352721176801107143/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell053Term01
