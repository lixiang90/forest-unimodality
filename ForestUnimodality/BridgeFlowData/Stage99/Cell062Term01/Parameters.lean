import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell062Term01
open CoupledFlow


def environment : Environment := ⟨(405/403), (203/201), (13080202604688154782213847802178439063261/5000000000000000000000000000000000000000), (18080202604688154782213847802178439063261/5000000000000000000000000000000000000000), 6, (132253548415547665317995922643511981193/100000000000000000000000000000000000000), (18169708558176710003907975761595164009119/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (405/808)

def qb : ℚ := (203/404)

def rho : ℚ := (277914611086527207358995156007/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (86421685310007458876928510127/500000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell062Term01
