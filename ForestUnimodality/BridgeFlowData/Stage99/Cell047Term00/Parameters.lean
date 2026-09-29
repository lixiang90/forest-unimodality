import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell047Term00
open CoupledFlow


def environment : Environment := ⟨(47/50), (9237/9775), (26551711685588985370881238537083843431261/10000000000000000000000000000000000000000), (36551711685588985370881238537083843431261/10000000000000000000000000000000000000000), 4, (3224337329415108998585813298430154825129/2500000000000000000000000000000000000000), (8879343594566207076342047137782544229291/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (47/97)

def qb : ℚ := (9237/19012)

def rho : ℚ := (132921556622766940758140821569/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (92481272772739619219565003089/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell047Term00
