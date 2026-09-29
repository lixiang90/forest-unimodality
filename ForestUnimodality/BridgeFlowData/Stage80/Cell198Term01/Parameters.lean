import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell198Term01
open CoupledFlow


def environment : Environment := ⟨(49/40), (99/80), (861441130963690682917954948336635051631/312500000000000000000000000000000000000), (1173941130963690682917954948336635051631/312500000000000000000000000000000000000), 13, (3417515214151537910329760229262068308983/2000000000000000000000000000000000000000), (4155358103791030260876068465173698149237/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (49/89)

def qb : ℚ := (99/179)

def rho : ℚ := (14722645878234583226135813339/50000000000000000000000000000)

def retention : ℚ := (1/4)

def rate : ℚ := (112555050652439563559170471337/500000000000000000000000000000)

def finish : ℚ := (138629436111989061883446424291635313613/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell198Term01
