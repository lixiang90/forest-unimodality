import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell146Term02
open CoupledFlow


def environment : Environment := ⟨(23607/21125), (94453/84475), (533471305314720287836999611737944810829/200000000000000000000000000000000000000), (733471305314720287836999611737944810829/200000000000000000000000000000000000000), 10, (1857037711463477066314898725338680566907/1250000000000000000000000000000000000000), (4839835380774059632021548075726276855581/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (23607/44732)

def qb : ℚ := (94453/178928)

def rho : ℚ := (57576373603398824440986939121/200000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (277801717735538695891081176913/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell146Term02
