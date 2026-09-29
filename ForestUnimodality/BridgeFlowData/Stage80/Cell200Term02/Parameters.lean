import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell200Term02
open CoupledFlow


def environment : Environment := ⟨(5/4), (116/91), (13945718107202825606074240612456711079603/5000000000000000000000000000000000000000), (18945718107202825606074240612456711079603/5000000000000000000000000000000000000000), 13, (8631186440533354919765707565792572076757/5000000000000000000000000000000000000000), (21233848313386741742073545034250999857333/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (5/9)

def qb : ℚ := (116/207)

def rho : ℚ := (295785290512109279395001213211/1000000000000000000000000000000)

def retention : ℚ := (1/5)

def rate : ℚ := (46268893037327662662207346851/200000000000000000000000000000)

def finish : ℚ := (3218875824868200749201518666452375279/2000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell200Term02
