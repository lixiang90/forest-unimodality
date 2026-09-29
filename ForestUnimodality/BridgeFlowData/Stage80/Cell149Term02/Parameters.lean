import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell149Term02
open CoupledFlow


def environment : Environment := ⟨(94503/84425), (28/25), (8338672938135023749678745897369691917/3125000000000000000000000000000000000), (11463672938135023749678745897369691917/3125000000000000000000000000000000000), 10, (7430601242710794187677993126455481773509/5000000000000000000000000000000000000000), (4845024034230651547034036001907190546053/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (94503/178928)

def qb : ℚ := (28/53)

def rho : ℚ := (288030442797158178857243271589/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (69505310408787473852554498713/250000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell149Term02
