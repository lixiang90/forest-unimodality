import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell175Term00
open CoupledFlow


def environment : Environment := ⟨(95549/85075), (15929/14175), (26652739806341628822989138176703811215657/10000000000000000000000000000000000000000), (36652739806341628822989138176703811215657/10000000000000000000000000000000000000000), 10, (7423141953404431791270186824909491227303/5000000000000000000000000000000000000000), (19394150025751255830500730202521758200047/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (95549/180624)

def qb : ℚ := (15929/30104)

def rho : ℚ := (288727306069252664421980544417/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100810334804378751813471848203/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell175Term00
