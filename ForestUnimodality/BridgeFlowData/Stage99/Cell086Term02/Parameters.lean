import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell086Term02
open CoupledFlow


def environment : Environment := ⟨(21967/20675), (10996/10325), (26610108485224851305076969964517513940849/10000000000000000000000000000000000000000), (36610108485224851305076969964517513940849/10000000000000000000000000000000000000000), 9, (2877761191261431142761429557865888150369/2000000000000000000000000000000000000000), (2360142306314973881095084433949126350157/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (21967/42642)

def qb : ℚ := (10996/21321)

def rho : ℚ := (140872475121561758233099018087/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (134266110153519956858506427033/500000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell086Term02
