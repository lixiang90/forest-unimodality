import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell087Term01
open CoupledFlow


def environment : Environment := ⟨1, (405/403), (26066847437962815288131139983364203717947/10000000000000000000000000000000000000000), (36066847437962815288131139983364203717947/10000000000000000000000000000000000000000), 6, (1648074406218858395472479761580740808001/1250000000000000000000000000000000000000), (9039030453202314475057618622068380263471/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (1/2)

def qb : ℚ := (405/808)

def rho : ℚ := (277949230037105751391465677179/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (66594736304998793059243550487/250000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell087Term01
