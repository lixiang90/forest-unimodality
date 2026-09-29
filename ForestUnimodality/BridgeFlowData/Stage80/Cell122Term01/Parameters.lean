import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell122Term01
open CoupledFlow


def environment : Environment := ⟨(4583/4195), (2294/2095), (6641498528323290974713702152820540488779/2500000000000000000000000000000000000000), (9141498528323290974713702152820540488779/2500000000000000000000000000000000000000), 9, (898013098300799246906272780166454597443/625000000000000000000000000000000000000), (19111959557050471174293217351169122698801/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (4583/8778)

def qb : ℚ := (2294/4389)

def rho : ℚ := (71469451989271273047616492601/250000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (44973249370336514932828356143/250000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell122Term01
