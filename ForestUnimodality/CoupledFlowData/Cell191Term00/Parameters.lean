import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell191Term00
open CoupledFlow


def environment : Environment := ⟨(48539/42625), (97103/85225), (26735710754519332289208059410916667222411/10000000000000000000000000000000000000000), (36735710754519332289208059410916667222411/10000000000000000000000000000000000000000), 10, (14886194877535015088306281917511407072541/10000000000000000000000000000000000000000), (391289074787864806642860141391145752413/200000000000000000000000000000000000000)⟩

def qa : ℚ := (48539/91164)

def qb : ℚ := (97103/182328)

def rho : ℚ := (144974237304025424052462528771/500000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (13070560090274197860723081009/250000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell191Term00
