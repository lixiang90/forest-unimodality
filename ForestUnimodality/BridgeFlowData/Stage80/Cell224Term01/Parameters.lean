import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell224Term01
open CoupledFlow


def environment : Environment := ⟨(33/20), (467/275), (15099308446873379827124793289580090427261/5000000000000000000000000000000000000000), (20099308446873379827124793289580090427261/5000000000000000000000000000000000000000), 15, (3201950347173682541973864777052394616719/1000000000000000000000000000000000000000), (6325051916906919393037249640319341125021/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (33/53)

def qb : ℚ := (467/742)

def rho : ℚ := (78283794635514097968243191709/250000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (146987733312358498602839739/1000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell224Term01
