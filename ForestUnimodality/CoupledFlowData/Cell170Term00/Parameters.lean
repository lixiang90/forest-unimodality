import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell170Term00
open CoupledFlow


def environment : Environment := ⟨(28/25), (95449/85175), (13317998997198373169246129768325094485813/5000000000000000000000000000000000000000), (18317998997198373169246129768325094485813/5000000000000000000000000000000000000000), 10, (593529215157630180319248331428827519609/400000000000000000000000000000000000000), (2419992202425463283715582979361632373849/1250000000000000000000000000000000000000)⟩

def qa : ℚ := (28/53)

def qb : ℚ := (95449/180624)

def rho : ℚ := (288481452556063263452917138219/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50322337138098137558915141073/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell170Term00
