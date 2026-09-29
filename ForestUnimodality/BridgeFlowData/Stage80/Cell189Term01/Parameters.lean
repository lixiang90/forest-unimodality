import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell189Term01
open CoupledFlow


def environment : Environment := ⟨(859/725), (1291/1085), (3398234140485570156675980278876396522277/1250000000000000000000000000000000000000), (4648234140485570156675980278876396522277/1250000000000000000000000000000000000000), 12, (7869295208334786582526477790460086333353/5000000000000000000000000000000000000000), (10102475211055338505502846026985568872491/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (859/1584)

def qb : ℚ := (1291/2376)

def rho : ℚ := (292234723944762475912810893789/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (22699748373618499757183226333/100000000000000000000000000000)

def finish : ℚ := (18886355519640093/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell189Term01
