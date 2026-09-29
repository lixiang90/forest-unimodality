import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell044Term01
open CoupledFlow


def environment : Environment := ⟨(4487/4825), (8999/9625), (12808001775753793276987640098725151253183/5000000000000000000000000000000000000000), (17808001775753793276987640098725151253183/5000000000000000000000000000000000000000), 4, (312621347113170707753865924728988026751/250000000000000000000000000000000000000), (4302357387779434753533391678705638856513/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (4487/9312)

def qb : ℚ := (8999/18624)

def rho : ℚ := (10853407015720801311685585927/40000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (267939609683480314571287882291/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell044Term01
