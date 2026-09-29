import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell074Term01
open CoupledFlow


def environment : Environment := ⟨(3193/3275), (49/50), (5182281614865518706430574963658165617677/2000000000000000000000000000000000000000), (7182281614865518706430574963658165617677/2000000000000000000000000000000000000000), 5, (13025355911725038476559101575511428262023/10000000000000000000000000000000000000000), (17774333289313657404802938041376268447787/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (3193/6468)

def qb : ℚ := (49/99)

def rho : ℚ := (275650285795017466046030782879/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (272909199363842534270480855591/1000000000000000000000000000000)

def finish : ℚ := (115129254649702284200899572734218210379/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell074Term01
