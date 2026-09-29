import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell168Term00
open CoupledFlow


def environment : Environment := ⟨(47239/42225), (94503/84425), (13314662363115981538236009512943700565577/5000000000000000000000000000000000000000), (18314662363115981538236009512943700565577/5000000000000000000000000000000000000000), 10, (1854377527625383170258181389251906318809/1250000000000000000000000000000000000000), (3869244695747003494831256386930426841073/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (47239/89464)

def qb : ℚ := (94503/178928)

def rho : ℚ := (18023884201211956687878153067/62500000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (20118294355910764812514375709/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell168Term00
