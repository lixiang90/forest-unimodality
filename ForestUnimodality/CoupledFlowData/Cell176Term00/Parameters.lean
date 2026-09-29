import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell176Term00
open CoupledFlow


def environment : Environment := ⟨(15929/14175), (95599/85025), (26656086395688228490853160025279695925171/10000000000000000000000000000000000000000), (36656086395688228490853160025279695925171/10000000000000000000000000000000000000000), 10, (3711973436598612780374418358652810590191/2500000000000000000000000000000000000000), (9700497174631828980359950076558800742843/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (15929/30104)

def qb : ℚ := (95599/180624)

def rho : ℚ := (72194115947706268728969732653/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50418343167935485629757592137/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell176Term00
