import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell130Term02
open CoupledFlow


def environment : Environment := ⟨(94453/84475), (47239/42225), (2702747573760435898150241875557009312899/1000000000000000000000000000000000000000), (3702747573760435898150241875557009312899/1000000000000000000000000000000000000000), 10, (3756629930693906242190329108814007338881/2500000000000000000000000000000000000000), (4887834565771406135225321804285454566419/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (94453/178928)

def qb : ℚ := (47239/89464)

def rho : ℚ := (285205747496316536660283009211/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (272682487471359677618585415027/1000000000000000000000000000000)

def finish : ℚ := (18971199848858813/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell130Term02
