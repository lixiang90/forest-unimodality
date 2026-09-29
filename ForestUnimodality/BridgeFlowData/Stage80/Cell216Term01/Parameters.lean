import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell216Term01
open CoupledFlow


def environment : Environment := ⟨(653/475), (7/5), (28639537875100076913414609166307756006051/10000000000000000000000000000000000000000), (38639537875100076913414609166307756006051/10000000000000000000000000000000000000000), 14, (20092589125814570948344409974825764470441/10000000000000000000000000000000000000000), (2253973042714171153282518868034619100353/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (653/1128)

def qb : ℚ := (7/12)

def rho : ℚ := (150967989114911869865583961491/500000000000000000000000000000)

def retention : ℚ := (3/10)

def rate : ℚ := (9883192865176942667047626217/50000000000000000000000000000)

def finish : ℚ := (120397280432593599262274621776183850293/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell216Term01
