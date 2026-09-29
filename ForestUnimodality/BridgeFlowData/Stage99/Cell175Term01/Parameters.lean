import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell175Term01
open CoupledFlow


def environment : Environment := ⟨(123/80), (63/40), (15017472439059640194606260905030611122707/5000000000000000000000000000000000000000), (20017472439059640194606260905030611122707/5000000000000000000000000000000000000000), 15, (31867540649000145471882239122408896834311/10000000000000000000000000000000000000000), (24487393469140919073013484213920941761759/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (123/203)

def qb : ℚ := (63/103)

def rho : ℚ := (305558300279406643340538351283/1000000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (195084595789976889260734596941/1000000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell175Term01
