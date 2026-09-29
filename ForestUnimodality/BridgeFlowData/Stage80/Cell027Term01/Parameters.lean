import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell027Term01
open CoupledFlow


def environment : Environment := ⟨(301/365), (17/20), (1582189623391410706648235000043850401337/625000000000000000000000000000000000000), (2207189623391410706648235000043850401337/625000000000000000000000000000000000000), 2, (5666022382559809026835645012651384558991/5000000000000000000000000000000000000000), (8112913210303563678490809729890909583293/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (301/666)

def qb : ℚ := (17/37)

def rho : ℚ := (130103077288361474298039803539/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (157294361384652654765659434467/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell027Term01
