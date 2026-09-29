import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell092Term01
open CoupledFlow


def environment : Environment := ⟨(10429/10175), (5227/5075), (204834061478359594275222341346986105751/78125000000000000000000000000000000000), (282959061478359594275222341346986105751/78125000000000000000000000000000000000), 7, (6779466855158754171369328992701560888459/5000000000000000000000000000000000000000), (1148535829429148203670422968915314598921/625000000000000000000000000000000000000)⟩

def qa : ℚ := (10429/20604)

def qb : ℚ := (5227/10302)

def rho : ℚ := (14008685281908645736848644367/50000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (135651106687406809036583473931/500000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell092Term01
