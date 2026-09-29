import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell125Term01
open CoupledFlow


def environment : Environment := ⟨(1531/1395), (11/10), (106375273662202507318381250051082289107/40000000000000000000000000000000000000), (146375273662202507318381250051082289107/40000000000000000000000000000000000000), 9, (14381200436594143324859527518806858067933/10000000000000000000000000000000000000000), (9584095299310878455370200896201816548673/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1531/2926)

def qb : ℚ := (11/21)

def rho : ℚ := (286283064457099538086762057857/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (54664216946476964395133205793/200000000000000000000000000000)

def finish : ℚ := (1416791880869979/625000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell125Term01
