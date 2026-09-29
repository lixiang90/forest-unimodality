import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell217Term02
open CoupledFlow


def environment : Environment := ⟨(7/5), (53/37), (5771809188080224219468278866266602590023/2000000000000000000000000000000000000000), (7771809188080224219468278866266602590023/2000000000000000000000000000000000000000), 14, (10113325714612302381944947385067456585157/5000000000000000000000000000000000000000), (11441830193562552323106077219781387146423/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (7/12)

def qb : ℚ := (53/90)

def rho : ℚ := (60617946183452810176323834313/200000000000000000000000000000)

def retention : ℚ := (1/4)

def rate : ℚ := (102011111402244884601897146879/500000000000000000000000000000)

def finish : ℚ := (138629436111989061883446424291635313613/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell217Term02
