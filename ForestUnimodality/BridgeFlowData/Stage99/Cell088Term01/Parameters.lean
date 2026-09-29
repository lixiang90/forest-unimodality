import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell088Term01
open CoupledFlow


def environment : Environment := ⟨(10996/10325), (7339/6875), (26630887671304466654877493988459557261209/10000000000000000000000000000000000000000), (36630887671304466654877493988459557261209/10000000000000000000000000000000000000000), 9, (14398507212034935834994166408773469572901/10000000000000000000000000000000000000000), (472833271105430351730944717147362970909/250000000000000000000000000000000000000)⟩

def qa : ℚ := (10996/21321)

def qb : ℚ := (7339/14214)

def rho : ℚ := (281905227496733596262751363727/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (176614991724102050585653060093/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell088Term01
