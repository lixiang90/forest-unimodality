import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell105Term00
open CoupledFlow


def environment : Environment := ⟨(407/401), (51/50), (2611067874930365614042465633245855406577/1000000000000000000000000000000000000000), (3611067874930365614042465633245855406577/1000000000000000000000000000000000000000), 7, (844422118231335420082438785278129341327/625000000000000000000000000000000000000), (18234105111034519437244133395597883736181/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (407/808)

def qb : ℚ := (51/101)

def rho : ℚ := (139834119030299925755241366451/500000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (68966644910026848797033865263/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell105Term00
