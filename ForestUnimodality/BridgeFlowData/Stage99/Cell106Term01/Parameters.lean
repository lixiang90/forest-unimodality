import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell106Term01
open CoupledFlow


def environment : Environment := ⟨(22647/20825), (109/100), (26814603653965400835024466668962385888617/10000000000000000000000000000000000000000), (36814603653965400835024466668962385888617/10000000000000000000000000000000000000000), 9, (14484272306596452616444633698869001486209/10000000000000000000000000000000000000000), (19199960757331237756065391707736363932341/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (22647/43472)

def qb : ℚ := (109/209)

def rho : ℚ := (56665675977993952387580881131/200000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (22425087700150731787379888247/125000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell106Term01
