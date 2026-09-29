import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell100Term01
open CoupledFlow


def environment : Environment := ⟨(21967/20675), (10996/10325), (13198286071393233622375120149173127505847/5000000000000000000000000000000000000000), (18198286071393233622375120149173127505847/5000000000000000000000000000000000000000), 9, (3572275477391761891606231154079907416529/2500000000000000000000000000000000000000), (18771010144087050036268169519282182829539/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (21967/42642)

def qb : ℚ := (10996/21321)

def rho : ℚ := (56679585940673976527366100839/200000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (266564077492143698079836254217/1000000000000000000000000000000)

def finish : ℚ := (4469040522087089/2000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell100Term01
