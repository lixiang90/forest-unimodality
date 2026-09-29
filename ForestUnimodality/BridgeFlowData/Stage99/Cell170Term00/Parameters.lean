import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell170Term00
open CoupledFlow


def environment : Environment := ⟨(653/475), (7/5), (29062065152665155214773674015787078340129/10000000000000000000000000000000000000000), (39062065152665155214773674015787078340129/10000000000000000000000000000000000000000), 14, (5087656519899011324040150565527833053069/2500000000000000000000000000000000000000), (11393102336194003604308988254604564515871/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (653/1128)

def qb : ℚ := (7/12)

def rho : ℚ := (74667497872105366537148454911/250000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (28483861148226603556624079973/1000000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell170Term00
