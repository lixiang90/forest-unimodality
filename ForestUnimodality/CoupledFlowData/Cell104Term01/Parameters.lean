import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell104Term01
open CoupledFlow


def environment : Environment := ⟨(203/201), (407/401), (5215989258320740406761419149174184277401/2000000000000000000000000000000000000000), (7215989258320740406761419149174184277401/2000000000000000000000000000000000000000), 7, (2699410666825370085340034493691349055961/2000000000000000000000000000000000000000), (18173933342429092484850851446249337876871/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (203/404)

def qb : ℚ := (407/808)

def rho : ℚ := (279220410815494811999635067933/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (50981225420973419600279844991/250000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell104Term01
