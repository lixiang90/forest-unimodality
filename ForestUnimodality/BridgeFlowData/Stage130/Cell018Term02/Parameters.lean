import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell018Term02
open CoupledFlow


def environment : Environment := ⟨(33/52), (101/154), (10843137254901960784313725490196078431373/5000000000000000000000000000000000000000), (15843137254901960784313725490196078431373/5000000000000000000000000000000000000000), 1, (217573580106769258712602803491852307683/250000000000000000000000000000000000000), (6275124951941560938100730488273740868897/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (33/85)

def qb : ℚ := (101/255)

def rho : ℚ := (1/4)

def retention : ℚ := (1/100)

def rate : ℚ := (219164385848132028035525740587/1000000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell018Term02
