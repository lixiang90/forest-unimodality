import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell180Term00
open CoupledFlow


def environment : Environment := ⟨(47837/42475), (95699/84925), (13334733694189385760472341747913649103167/5000000000000000000000000000000000000000), (18334733694189385760472341747913649103167/5000000000000000000000000000000000000000), 10, (14854330480611427079279862255202886461099/10000000000000000000000000000000000000000), (971418903246650515928914558936568952921/500000000000000000000000000000000000000)⟩

def qa : ℚ := (47837/90312)

def qb : ℚ := (95699/180624)

def rho : ℚ := (2889730472272468332886303369/10000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50512583662961912226586616731/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell180Term00
