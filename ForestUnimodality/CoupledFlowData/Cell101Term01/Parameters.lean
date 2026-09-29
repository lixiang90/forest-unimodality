import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell101Term01
open CoupledFlow


def environment : Environment := ⟨(405/403), (203/201), (26049170643101065743102084304610093993429/10000000000000000000000000000000000000000), (36049170643101065743102084304610093993429/10000000000000000000000000000000000000000), 6, (6588446885661924213073697074881051084511/5000000000000000000000000000000000000000), (3622763188390849676163229264275172812211/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (405/808)

def qb : ℚ := (203/404)

def rho : ℚ := (278772154011212467883159759871/1000000000000000000000000000000)

def retention : ℚ := (1/2)

def rate : ℚ := (202824429635802291184018667971/1000000000000000000000000000000)

def finish : ℚ := (13862943611198906188344642429163531361/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell101Term01
