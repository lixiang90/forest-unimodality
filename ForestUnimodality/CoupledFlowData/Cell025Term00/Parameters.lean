import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell025Term00
open CoupledFlow


def environment : Environment := ⟨(67/86), (4/5), (24833429586335655893821467838450695219001/10000000000000000000000000000000000000000), (34833429586335655893821467838450695219001/10000000000000000000000000000000000000000), 2, (2786735096545923951057951669616839952381/2500000000000000000000000000000000000000), (3096304852118724968339686030084506241689/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (67/153)

def qb : ℚ := (4/9)

def rho : ℚ := (255182707946041386065816992911/1000000000000000000000000000000)

def retention : ℚ := (7/10)

def rate : ℚ := (118952202164032185701210973187/1000000000000000000000000000000)

def finish : ℚ := (17833747196936618945631935562059223897/50000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell025Term00
