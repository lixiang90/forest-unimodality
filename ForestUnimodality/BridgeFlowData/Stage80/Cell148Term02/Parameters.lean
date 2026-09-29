import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell148Term02
open CoupledFlow


def environment : Environment := ⟨(47239/42225), (94503/84425), (13340178947131322914015259424686267663361/5000000000000000000000000000000000000000), (18340178947131322914015259424686267663361/5000000000000000000000000000000000000000), 10, (14859569150622133805816233784711211758917/10000000000000000000000000000000000000000), (19373177267289092923893231483179003319667/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (47239/89464)

def qb : ℚ := (94503/178928)

def rho : ℚ := (143990461409856700272846864677/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (277948067298548966148725760983/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell148Term02
