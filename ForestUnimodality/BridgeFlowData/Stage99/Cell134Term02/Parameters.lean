import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell134Term02
open CoupledFlow


def environment : Environment := ⟨(95449/85175), (47737/42575), (13523461638210382266557778279266184031331/5000000000000000000000000000000000000000), (18523461638210382266557778279266184031331/5000000000000000000000000000000000000000), 10, (15035871903260474772234992930987801680751/10000000000000000000000000000000000000000), (9791107363619995330173937701715495472403/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (95449/180624)

def qb : ℚ := (47737/90312)

def rho : ℚ := (28535633093743617895016533147/100000000000000000000000000000)

def retention : ℚ := (3/20)

def rate : ℚ := (68242221767491300566960630129/250000000000000000000000000000)

def finish : ℚ := (914618989546949/500000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell134Term02
