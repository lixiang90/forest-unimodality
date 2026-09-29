import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell187Term00
open CoupledFlow


def environment : Environment := ⟨(8069/7125), (12116/10675), (3341385921564135332248471665779970531839/1250000000000000000000000000000000000000), (4591385921564135332248471665779970531839/1250000000000000000000000000000000000000), 10, (14883970992501114409500623512500858886883/10000000000000000000000000000000000000000), (19526736633116954476950544584297353504019/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (8069/15194)

def qb : ℚ := (12116/22791)

def rho : ℚ := (72365589229353797502209194131/250000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (10130840048582174587767024409/100000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell187Term00
