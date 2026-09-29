import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell199Term00
open CoupledFlow


def environment : Environment := ⟨(859/725), (1291/1085), (27133851581975581967582850366213772373753/10000000000000000000000000000000000000000), (37133851581975581967582850366213772373753/10000000000000000000000000000000000000000), 12, (7856261386564282822394542156503174204863/5000000000000000000000000000000000000000), (315260695446196840278760652243673585691/156250000000000000000000000000000000000)⟩

def qa : ℚ := (859/1584)

def qb : ℚ := (1291/2376)

def rho : ℚ := (36580515163548598135988935517/125000000000000000000000000000)

def retention : ℚ := (19/20)

def rate : ℚ := (13415034723986104302295308531/500000000000000000000000000000)

def finish : ℚ := (5129329438755053342619614425468723841/100000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell199Term00
