import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell042Term02
open CoupledFlow


def environment : Environment := ⟨(23/25), (2983/3225), (26701380727678487982297058956159739660201/10000000000000000000000000000000000000000), (36701380727678487982297058956159739660201/10000000000000000000000000000000000000000), 4, (6480050741562634755151939353401041796359/5000000000000000000000000000000000000000), (17635344508805562121648216312213998615719/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (23/48)

def qb : ℚ := (2983/6208)

def rho : ℚ := (261847925659199501371102085081/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (66216523333119320225539096197/250000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell042Term02
