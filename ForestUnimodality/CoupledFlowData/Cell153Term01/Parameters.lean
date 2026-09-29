import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell153Term01
open CoupledFlow


def environment : Environment := ⟨(2294/2095), (1531/1395), (829041862697387639675215422294729536553/312500000000000000000000000000000000000), (1141541862697387639675215422294729536553/312500000000000000000000000000000000000), 9, (14351095532627224457899277847166110609133/10000000000000000000000000000000000000000), (4778402164838552225133984447117514478367/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (2294/4389)

def qb : ℚ := (1531/2926)

def rho : ℚ := (286476527424703293081212469329/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (143148154961449025001645873949/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell153Term01
