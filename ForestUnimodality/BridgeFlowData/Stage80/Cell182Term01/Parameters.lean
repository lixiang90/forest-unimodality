import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell182Term01
open CoupledFlow


def environment : Environment := ⟨(2557/2195), (427/365), (27041854023314392311433121528507136646523/10000000000000000000000000000000000000000), (37041854023314392311433121528507136646523/10000000000000000000000000000000000000000), 12, (3133284170175578048993603270409275704427/2000000000000000000000000000000000000000), (19970797560549552420431746076606751702103/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2557/4752)

def qb : ℚ := (427/792)

def rho : ℚ := (291098503763917921339997039819/1000000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (222149204557596654274635024741/1000000000000000000000000000000)

def finish : ℚ := (16094379124341003/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell182Term01
