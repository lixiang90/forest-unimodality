import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell039Term00
open CoupledFlow


def environment : Environment := ⟨(1733/1915), (869/955), (25444104405547442783616444498439561280879/10000000000000000000000000000000000000000), (35444104405547442783616444498439561280879/10000000000000000000000000000000000000000), 4, (12432713595020374532534562662161478521333/10000000000000000000000000000000000000000), (1055404561692047963917307095296874271967/625000000000000000000000000000000000000)⟩

def qa : ℚ := (1733/3648)

def qb : ℚ := (869/1824)

def rho : ℚ := (268831980148396542165809869071/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (163285455678645147729374615397/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell039Term00
