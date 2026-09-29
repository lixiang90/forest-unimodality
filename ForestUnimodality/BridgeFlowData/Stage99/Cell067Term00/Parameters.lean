import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell067Term00
open CoupledFlow


def environment : Environment := ⟨(407/401), (51/50), (26249141458149672059747306771948428068191/10000000000000000000000000000000000000000), (36249141458149672059747306771948428068191/10000000000000000000000000000000000000000), 7, (13572476258454551129101246360319259554337/10000000000000000000000000000000000000000), (9152010962206105322015409135491929858801/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (407/808)

def qb : ℚ := (51/101)

def rho : ℚ := (27859997491663628293951163033/100000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (95846638486223506275272993133/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell067Term00
