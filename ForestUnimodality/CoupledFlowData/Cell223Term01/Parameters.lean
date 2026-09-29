import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell223Term01
open CoupledFlow


def environment : Environment := ⟨(236/135), (9/5), (30565292485251164686566916807957583673057/10000000000000000000000000000000000000000), (40565292485251164686566916807957583673057/10000000000000000000000000000000000000000), 15, (32359894364111554130983325311546557678059/10000000000000000000000000000000000000000), (651942200655822289605539734413604023317/250000000000000000000000000000000000000)⟩

def qa : ℚ := (236/371)

def qb : ℚ := (9/14)

def rho : ℚ := (158474672182106055633464215881/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (113172794545140242183482100549/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell223Term01
