import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell191Term01
open CoupledFlow


def environment : Environment := ⟨(2587/2165), (6/5), (27257673913857820849943218923772211672219/10000000000000000000000000000000000000000), (37257673913857820849943218923772211672219/10000000000000000000000000000000000000000), 12, (7887283798775251348034179633635328853043/5000000000000000000000000000000000000000), (508059189734424829771952985324166522803/250000000000000000000000000000000000000)⟩

def qa : ℚ := (2587/4752)

def qb : ℚ := (6/11)

def rho : ℚ := (146400590309441228767112474667/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (44272116163326308336119543571/250000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell191Term01
