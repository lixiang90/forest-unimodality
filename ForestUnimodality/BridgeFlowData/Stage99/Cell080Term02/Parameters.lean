import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell080Term02
open CoupledFlow


def environment : Environment := ⟨(5381/5125), (10787/10225), (6636943605351259277016667575593350642209/2500000000000000000000000000000000000000), (9136943605351259277016667575593350642209/2500000000000000000000000000000000000000), 9, (14359702837421797770064640648742816277411/10000000000000000000000000000000000000000), (938132597286541346099169932780558474943/500000000000000000000000000000000000000)⟩

def qa : ℚ := (5381/10506)

def qb : ℚ := (10787/21012)

def rho : ℚ := (280932734546252130194946275727/1000000000000000000000000000000)

def retention : ℚ := (1/100)

def rate : ℚ := (140053597658056672780153744833/500000000000000000000000000000)

def finish : ℚ := (230258509299404568401799145468436420759/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell080Term02
