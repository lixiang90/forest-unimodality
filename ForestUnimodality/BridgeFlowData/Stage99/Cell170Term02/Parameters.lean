import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell170Term02
open CoupledFlow


def environment : Environment := ⟨(653/475), (7/5), (29062065152665155214773674015787078340129/10000000000000000000000000000000000000000), (39062065152665155214773674015787078340129/10000000000000000000000000000000000000000), 14, (5087656519899011324040150565527833053069/2500000000000000000000000000000000000000), (11393102336194003604308988254604564515871/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (653/1128)

def qb : ℚ := (7/12)

def rho : ℚ := (74667497872105366537148454911/250000000000000000000000000000)

def retention : ℚ := (1/4)

def rate : ℚ := (99414243445210145440856106739/500000000000000000000000000000)

def finish : ℚ := (138629436111989061883446424291635313613/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell170Term02
