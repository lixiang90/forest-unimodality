import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell051Term02
open CoupledFlow


def environment : Environment := ⟨(9237/9775), (4631/4875), (6428949855509869212032756281222862623663/2500000000000000000000000000000000000000), (8928949855509869212032756281222862623663/2500000000000000000000000000000000000000), 4, (12546729750392957167907539753933583606063/10000000000000000000000000000000000000000), (1739952315626602327831840704327501654121/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (9237/19012)

def qb : ℚ := (4631/9506)

def rho : ℚ := (136400698935543597779231127479/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (134409233240311743025333514251/500000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell051Term02
