import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell058Term00
open CoupledFlow


def environment : Environment := ⟨(197/199), (395/397), (26189481607318259712783535749618372032201/10000000000000000000000000000000000000000), (36189481607318259712783535749618372032201/10000000000000000000000000000000000000000), 5, (13145663380440541605922820410781660177001/10000000000000000000000000000000000000000), (451226175343772493262294716575102807851/250000000000000000000000000000000000000)⟩

def qa : ℚ := (197/396)

def qb : ℚ := (395/792)

def rho : ℚ := (275625597044484191915371068273/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (47733322333981119841595679343/500000000000000000000000000000)

def finish : ℚ := (2231435513142097/10000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell058Term00
