import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell128Term00
open CoupledFlow


def environment : Environment := ⟨(10996/10325), (7339/6875), (26361093939516429495758708065565463873683/10000000000000000000000000000000000000000), (36361093939516429495758708065565463873683/10000000000000000000000000000000000000000), 9, (1427253478407564603253785667655989958471/1000000000000000000000000000000000000000), (4693507605566889617091831266589013285651/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (10996/21321)

def qb : ℚ := (7339/14214)

def rho : ℚ := (28399692098272751141556309037/100000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (48915218497521997821096372393/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell128Term00
