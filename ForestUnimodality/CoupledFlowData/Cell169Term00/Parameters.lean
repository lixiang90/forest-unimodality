import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell169Term00
open CoupledFlow


def environment : Environment := ⟨(94503/84425), (28/25), (13316353553151138701874226199115973994997/5000000000000000000000000000000000000000), (18316353553151138701874226199115973994997/5000000000000000000000000000000000000000), 10, (14836647308126747969779284630978663727003/10000000000000000000000000000000000000000), (302392629415231063474338640079744853691/156250000000000000000000000000000000000)⟩

def qa : ℚ := (94503/178928)

def qb : ℚ := (28/53)

def rho : ℚ := (28843180235596837377227646349/100000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100618064268314549599121163843/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell169Term00
