import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell163Term01
open CoupledFlow


def environment : Environment := ⟨(111/100), (23557/21175), (26611051470606621907532894810117814605491/10000000000000000000000000000000000000000), (36611051470606621907532894810117814605491/10000000000000000000000000000000000000000), 10, (14826229831006434244193599423572669988743/10000000000000000000000000000000000000000), (1928030357446749960376804978632623979839/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (111/211)

def qb : ℚ := (23557/44732)

def rho : ℚ := (71921621146840380107063868321/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (71935827156534222555432786599/500000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell163Term01
