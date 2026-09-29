import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell107Term01
open CoupledFlow


def environment : Environment := ⟨(11153/10375), (22331/20725), (529360142998574458170551792208998653797/200000000000000000000000000000000000000), (729360142998574458170551792208998653797/200000000000000000000000000000000000000), 9, (7161229087373834982689812718883756665287/5000000000000000000000000000000000000000), (4728534162863818696989557806060464551381/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (11153/21528)

def qb : ℚ := (22331/43056)

def rho : ℚ := (35555146181341804442218058571/125000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (268965815197165005187780856193/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell107Term01
