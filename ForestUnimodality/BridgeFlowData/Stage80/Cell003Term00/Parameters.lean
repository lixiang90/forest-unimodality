import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell003Term00
open CoupledFlow


def environment : Environment := ⟨(19/51), (39/101), (6142857142857142857142857142857142857143/5000000000000000000000000000000000000000), (11142857142857142857142857142857142857143/5000000000000000000000000000000000000000), 0, (2225541869353371199160037520056189111471/5000000000000000000000000000000000000000), (388010204081632653061224489795918367347/625000000000000000000000000000000000000)⟩

def qa : ℚ := (19/70)

def qb : ℚ := (39/140)

def rho : ℚ := (1/4)

def retention : ℚ := (1/20)

def rate : ℚ := (1405236069481148060102671043/8000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell003Term00
