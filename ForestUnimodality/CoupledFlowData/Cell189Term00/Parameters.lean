import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell189Term00
open CoupledFlow


def environment : Environment := ⟨(24257/21325), (32351/28425), (13364553138569401925113706892214440117771/5000000000000000000000000000000000000000), (18364553138569401925113706892214440117771/5000000000000000000000000000000000000000), 10, (14883018066694646923121994745038643033959/10000000000000000000000000000000000000000), (19550864110367866318262259170397174945703/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (24257/45582)

def qb : ℚ := (32351/60776)

def rho : ℚ := (289851285666033842761104246837/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50813704576437186363577576573/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell189Term00
