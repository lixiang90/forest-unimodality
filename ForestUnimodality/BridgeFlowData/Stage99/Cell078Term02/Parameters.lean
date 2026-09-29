import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell078Term02
open CoupledFlow


def environment : Environment := ⟨(3579/3425), (5381/5125), (13252748353821766701539271778232896363063/5000000000000000000000000000000000000000), (18252748353821766701539271778232896363063/5000000000000000000000000000000000000000), 8, (13811157398660753004929068068143239083021/10000000000000000000000000000000000000000), (18697513590693875237194521499842226409603/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (3579/7004)

def qb : ℚ := (5381/10506)

def rho : ℚ := (70151560775110727133983890029/250000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (6968995988511668590097130223/25000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell078Term02
