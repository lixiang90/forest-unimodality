import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell137Term02
open CoupledFlow


def environment : Environment := ⟨(23881/21275), (95549/85075), (13530733896434313079671823284624867908251/5000000000000000000000000000000000000000), (18530733896434313079671823284624867908251/5000000000000000000000000000000000000000), 10, (15042866163255091873796267051018524751359/10000000000000000000000000000000000000000), (1960529157886440539960983084222054105507/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (23881/45156)

def qb : ℚ := (95549/180624)

def rho : ℚ := (35683552463626807798966871253/125000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (273256472304637617880217548479/1000000000000000000000000000000)

def finish : ℚ := (9154522058058609/5000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell137Term02
