import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell089Term00
open CoupledFlow


def environment : Environment := ⟨(203/201), (407/401), (6532169051103212533569995390920596880073/2500000000000000000000000000000000000000), (9032169051103212533569995390920596880073/2500000000000000000000000000000000000000), 7, (6759388503435518182940314552699391843173/5000000000000000000000000000000000000000), (18198479226727759906747465960914271931633/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (203/404)

def qb : ℚ := (407/808)

def rho : ℚ := (8713868805301049154327541571/31250000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (34746125404568448541641115421/200000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell089Term00
