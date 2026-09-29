import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell148Term03
open CoupledFlow


def environment : Environment := ⟨(31933/28275), (113/100), (13557374461225280057886136132216905207079/5000000000000000000000000000000000000000), (18557374461225280057886136132216905207079/5000000000000000000000000000000000000000), 10, (15068487658543537206769016439549498478967/10000000000000000000000000000000000000000), (9844992085063176744324569872960142199061/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (31933/60208)

def qb : ℚ := (113/213)

def rho : ℚ := (142939517934870200637771252367/500000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (137424784913988416756266732809/500000000000000000000000000000)

def finish : ℚ := (1897119984885881302039978339220015071/1000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell148Term03
