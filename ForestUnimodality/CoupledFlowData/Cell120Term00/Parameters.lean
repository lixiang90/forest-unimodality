import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell120Term00
open CoupledFlow


def environment : Environment := ⟨(5381/5125), (10787/10225), (3289558959017490377867883920365670174853/1250000000000000000000000000000000000000), (4539558959017490377867883920365670174853/1250000000000000000000000000000000000000), 9, (14251696994486150047854103796079276729031/10000000000000000000000000000000000000000), (9321953643807665849240598486385776542193/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (5381/10506)

def qb : ℚ := (10787/21012)

def rho : ℚ := (141361009715896245121689758251/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (19550203102286092436543069687/200000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell120Term00
