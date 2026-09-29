import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell087Term01
open CoupledFlow


def environment : Environment := ⟨(131/133), (197/199), (6481391490508461586178292272070234379507/2500000000000000000000000000000000000000), (8981391490508461586178292272070234379507/2500000000000000000000000000000000000000), 5, (13031481964474228265909800067014636420389/10000000000000000000000000000000000000000), (17872061854850171035122460379776122957201/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (131/264)

def qb : ℚ := (197/396)

def rho : ℚ := (55389495937292011283385574343/200000000000000000000000000000)

def retention : ℚ := (2/5)

def rate : ℚ := (57816966684354992801929636581/250000000000000000000000000000)

def finish : ℚ := (91629073187415506518352721176801107143/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell087Term01
