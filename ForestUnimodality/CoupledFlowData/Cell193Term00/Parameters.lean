import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell193Term00
open CoupledFlow


def environment : Environment := ⟨(57/50), (29/25), (27031208360661066548374480007781017066181/10000000000000000000000000000000000000000), (37031208360661066548374480007781017066181/10000000000000000000000000000000000000000), 11, (1906223078294966513494964158911572472221/1250000000000000000000000000000000000000), (4971782603977643193994721852896525439441/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (57/107)

def qb : ℚ := (29/54)

def rho : ℚ := (290045645719485273281909003823/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20164932660356614379975610151/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell193Term00
