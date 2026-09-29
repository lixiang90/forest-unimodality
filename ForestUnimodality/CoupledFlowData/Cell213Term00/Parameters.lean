import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell213Term00
open CoupledFlow


def environment : Environment := ⟨(653/475), (7/5), (7146370678657623630068829363254811147467/2500000000000000000000000000000000000000), (9646370678657623630068829363254811147467/2500000000000000000000000000000000000000), 14, (2507446559043349373338926568009115246289/1250000000000000000000000000000000000000), (22508198250201121803493935180927892677423/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (653/1128)

def qb : ℚ := (7/12)

def rho : ℚ := (302358966271089449594507287049/1000000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (28483888980696271497849592881/1000000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell213Term00
