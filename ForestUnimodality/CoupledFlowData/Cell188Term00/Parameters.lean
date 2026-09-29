import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell188Term00
open CoupledFlow


def environment : Environment := ⟨(12116/10675), (24257/21325), (26744292917761644656078959022623845281217/10000000000000000000000000000000000000000), (36744292917761644656078959022623845281217/10000000000000000000000000000000000000000), 10, (7445161473634690962824936132086538871841/5000000000000000000000000000000000000000), (2444238716231583230284178263930352482851/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (12116/22791)

def qb : ℚ := (24257/45582)

def rho : ℚ := (289656856074296850362447932191/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (101444833110264849252830581293/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell188Term00
