import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell151Term01
open CoupledFlow


def environment : Environment := ⟨(95449/85175), (47737/42575), (26690419802625167665134264055427810214057/10000000000000000000000000000000000000000), (36690419802625167665134264055427810214057/10000000000000000000000000000000000000000), 10, (14864409198721304855684492693958344134361/10000000000000000000000000000000000000000), (4848443645689159881384850194918608203197/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (95449/180624)

def qb : ℚ := (47737/90312)

def rho : ℚ := (288129003580486265177183737409/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (278167052639878935707802231259/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell151Term01
