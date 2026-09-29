import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell140Term00
open CoupledFlow


def environment : Environment := ⟨(95599/85025), (11953/10625), (27076006603661973247822837248063845656521/10000000000000000000000000000000000000000), (37076006603661973247822837248063845656521/10000000000000000000000000000000000000000), 10, (7524928800217336943527033440187388564247/5000000000000000000000000000000000000000), (3925675497684219738074465175180327284369/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (95599/180624)

def qb : ℚ := (11953/22578)

def rho : ℚ := (285580464486365869077084288983/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (10086241921164630369853338373/100000000000000000000000000000)

def finish : ℚ := (22313309274318957/100000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell140Term00
