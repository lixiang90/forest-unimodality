import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell033Term00
open CoupledFlow


def environment : Environment := ⟨(1687/1885), (9/10), (26889920936075056896244376371807486875601/10000000000000000000000000000000000000000), (36889920936075056896244376371807486875601/10000000000000000000000000000000000000000), 3, (12440725867756076085361571556651054409949/10000000000000000000000000000000000000000), (1747417307498292168769470459717196746739/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (1687/3572)

def qb : ℚ := (9/19)

def rho : ℚ := (256809555838920122246328633407/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (45126100884842947718719376107/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell033Term00
