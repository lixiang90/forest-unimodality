import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell178Term00
open CoupledFlow


def environment : Environment := ⟨(11953/10625), (31883/28325), (26662778032643384397183546657478970171059/10000000000000000000000000000000000000000), (36662778032643384397183546657478970171059/10000000000000000000000000000000000000000), 10, (14851112670873023951438429910363344499323/10000000000000000000000000000000000000000), (9707342479527380287797327747810938795209/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (11953/22578)

def qb : ℚ := (31883/60208)

def rho : ℚ := (144437382229451377944381543617/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50444694675635651567339170879/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell178Term00
