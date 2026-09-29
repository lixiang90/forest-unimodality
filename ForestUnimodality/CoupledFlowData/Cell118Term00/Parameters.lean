import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell118Term00
open CoupledFlow


def environment : Environment := ⟨(3579/3425), (5381/5125), (26287208654760533365571401334618736649617/10000000000000000000000000000000000000000), (36287208654760533365571401334618736649617/10000000000000000000000000000000000000000), 8, (6856492284086306119439489362541951396717/5000000000000000000000000000000000000000), (9292855024332116411580987558613336279821/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (3579/7004)

def qb : ℚ := (5381/10506)

def rho : ℚ := (56458849624431326278127443343/200000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (97444714122472307943307455513/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell118Term00
