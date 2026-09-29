import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell162Term01
open CoupledFlow


def environment : Environment := ⟨(7977/7075), (95749/84875), (3340921219918216131271247853536141730437/1250000000000000000000000000000000000000), (4590921219918216131271247853536141730437/1250000000000000000000000000000000000000), 10, (14882182783795837496575723521534340476811/10000000000000000000000000000000000000000), (4867305738838130883527003174863052911547/2500000000000000000000000000000000000000)⟩

def qa : ℚ := (7977/15052)

def qb : ℚ := (95749/180624)

def rho : ℚ := (288668210212718158456382970189/1000000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (55943506495540301438673235611/200000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell162Term01
