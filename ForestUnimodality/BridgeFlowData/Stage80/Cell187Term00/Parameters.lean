import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell187Term00
open CoupledFlow


def environment : Environment := ⟨(2567/2185), (643/545), (6778483357532382901901199684655476853973/2500000000000000000000000000000000000000), (9278483357532382901901199684655476853973/2500000000000000000000000000000000000000), 12, (15702541644744416667988596622580575755341/10000000000000000000000000000000000000000), (5021940066408520375355615654236928970627/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (2567/4752)

def qb : ℚ := (643/1188)

def rho : ℚ := (291667167138043896598646980797/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (174479200251963065924589977331/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell187Term00
