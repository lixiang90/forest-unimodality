import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell190Term00
open CoupledFlow


def environment : Environment := ⟨(32351/28425), (48539/42625), (6683102189615830259374647091138561682109/2500000000000000000000000000000000000000), (9183102189615830259374647091138561682109/2500000000000000000000000000000000000000), 10, (14884606590928219911639367101931469423569/10000000000000000000000000000000000000000), (19557658601279574611021280117448758083801/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (32351/60776)

def qb : ℚ := (48539/91164)

def rho : ℚ := (289899882590758409559448555741/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (25413391944076440977736120777/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell190Term00
