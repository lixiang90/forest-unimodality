import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell171Term00
open CoupledFlow


def environment : Environment := ⟨(95449/85175), (47737/42575), (13319673751048761121331571855906629056601/5000000000000000000000000000000000000000), (18319673751048761121331571855906629056601/5000000000000000000000000000000000000000), 10, (1854980205523738849470222486564040975289/1250000000000000000000000000000000000000), (19366778852285736328483595661383088654331/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (95449/180624)

def qb : ℚ := (47737/90312)

def rho : ℚ := (144265316106883885995974723203/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100671017038518644606298855117/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell171Term00
