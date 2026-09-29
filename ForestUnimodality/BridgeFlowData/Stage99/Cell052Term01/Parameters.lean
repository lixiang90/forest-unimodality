import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell052Term01
open CoupledFlow


def environment : Environment := ⟨(9529/9875), (4777/4925), (13184715212883831433546403284306387502571/5000000000000000000000000000000000000000), (18184715212883831433546403284306387502571/5000000000000000000000000000000000000000), 5, (13223502433792311666869869435576654514737/10000000000000000000000000000000000000000), (8953657449180175505880351318195383745597/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (9529/19404)

def qb : ℚ := (4777/9702)

def rho : ℚ := (33845230795089379886226210021/125000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (171930219256012646283108407201/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell052Term01
