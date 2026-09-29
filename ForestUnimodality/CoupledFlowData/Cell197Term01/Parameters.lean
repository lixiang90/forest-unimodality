import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell197Term01
open CoupledFlow


def environment : Environment := ⟨(2567/2185), (643/545), (2706201252896068308531444154815085601369/1000000000000000000000000000000000000000), (3706201252896068308531444154815085601369/1000000000000000000000000000000000000000), 12, (15676522986011820853683217440423236497917/10000000000000000000000000000000000000000), (20059658296398753555435341679680976781821/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (2567/4752)

def qb : ℚ := (643/1188)

def rho : ℚ := (5841515388003881937780099389/20000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100274283937419885898198966193/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell197Term01
