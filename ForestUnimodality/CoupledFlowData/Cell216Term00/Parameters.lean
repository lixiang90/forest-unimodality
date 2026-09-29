import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell216Term00
open CoupledFlow


def environment : Environment := ⟨(107/73), (3/2), (14582800656819156267665642050786206007663/5000000000000000000000000000000000000000), (19582800656819156267665642050786206007663/5000000000000000000000000000000000000000), 14, (20413844646222134857517734214933761967693/10000000000000000000000000000000000000000), (5874840197045746880299692615235861802299/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (107/180)

def qb : ℚ := (3/5)

def rho : ℚ := (306391312721179631652894559259/1000000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (57436072925801573248260771951/1000000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell216Term00
