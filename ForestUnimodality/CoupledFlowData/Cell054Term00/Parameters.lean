import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell054Term00
open CoupledFlow


def environment : Environment := ⟨(47/50), (9237/9775), (25635338476291103098218130438530509420741/10000000000000000000000000000000000000000), (35635338476291103098218130438530509420741/10000000000000000000000000000000000000000), 4, (12512967404169253166705672562476632615597/10000000000000000000000000000000000000000), (865673315552022194714498398013639584261/500000000000000000000000000000000000000)⟩

def qa : ℚ := (47/97)

def qb : ℚ := (9237/19012)

def rho : ℚ := (17042459192956493318899060431/62500000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (46241962238200446071680986243/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell054Term00
