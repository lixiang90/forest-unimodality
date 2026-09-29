import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell177Term00
open CoupledFlow


def environment : Environment := ⟨(95599/85025), (11953/10625), (26659432470995959500186757716167160063501/10000000000000000000000000000000000000000), (36659432470995959500186757716167160063501/10000000000000000000000000000000000000000), 10, (464046979198562400309608445307854236239/312500000000000000000000000000000000000), (19407839327035818225960329302034992658297/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (95599/180624)

def qb : ℚ := (11953/22578)

def rho : ℚ := (57765123317446141447204211153/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (50431518925751057989411777117/500000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell177Term00
