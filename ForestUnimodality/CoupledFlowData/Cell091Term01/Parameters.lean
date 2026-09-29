import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell091Term01
open CoupledFlow


def environment : Environment := ⟨(197/199), (395/397), (5191427626874802873882766640869662434203/2000000000000000000000000000000000000000), (7191427626874802873882766640869662434203/2000000000000000000000000000000000000000), 5, (3261285706739691854474313996464871083189/2500000000000000000000000000000000000000), (8966584320124833128736404113458070269919/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (197/396)

def qb : ℚ := (395/792)

def rho : ℚ := (277406601089086571533017377519/1000000000000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (232338834969413839998620767193/1000000000000000000000000000000)

def finish : ℚ := (91629073187415506518352721176801107143/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell091Term01
