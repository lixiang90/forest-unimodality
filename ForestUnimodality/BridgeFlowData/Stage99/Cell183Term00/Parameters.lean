import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell183Term00
open CoupledFlow


def environment : Environment := ⟨(83/43), 2, (31849995363797737800910741681439676541659/10000000000000000000000000000000000000000), (41849995363797737800910741681439676541659/10000000000000000000000000000000000000000), 15, (33551960761572028434794104261794204616169/10000000000000000000000000000000000000000), (27899996909198491867273827787626451027773/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (83/126)

def qb : ℚ := (2/3)

def rho : ℚ := (159299101677646887236700122211/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (181576817074448272638346562523/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell183Term00
