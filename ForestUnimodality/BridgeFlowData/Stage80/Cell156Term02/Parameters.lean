import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell156Term02
open CoupledFlow


def environment : Environment := ⟨(15929/14175), (95599/85025), (6676805925237539920844823256656796432589/2500000000000000000000000000000000000000), (9176805925237539920844823256656796432589/2500000000000000000000000000000000000000), 10, (7436246118787612224900486504607699370333/5000000000000000000000000000000000000000), (19428059829187341192595541201903026888101/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (15929/30104)

def qb : ℚ := (95599/180624)

def rho : ℚ := (288374165586481437942392199167/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (139667062492767243881982950277/500000000000000000000000000000)

def finish : ℚ := (4605170185988091/1000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell156Term02
