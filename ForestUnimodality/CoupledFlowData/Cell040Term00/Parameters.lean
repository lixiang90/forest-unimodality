import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell040Term00
open CoupledFlow


def environment : Environment := ⟨(9/10), (1733/1915), (5072571263281553682283668960224960887389/2000000000000000000000000000000000000000), (7072571263281553682283668960224960887389/2000000000000000000000000000000000000000), 4, (3099653146688677481219016973537379416769/2500000000000000000000000000000000000000), (16799295503381212351148023996806273599021/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (9/19)

def qb : ℚ := (1733/3648)

def rho : ℚ := (268674464704360484040076183601/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (81220896305485496944549329523/500000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell040Term00
