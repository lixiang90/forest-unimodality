import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell024Term01
open CoupledFlow


def environment : Environment := ⟨(22/29), (67/86), (1235279216205247937634191436629876175823/500000000000000000000000000000000000000), (1735279216205247937634191436629876175823/500000000000000000000000000000000000000), 2, (346805899874945429044725058335598056459/312500000000000000000000000000000000000), (7598935129787687047156263153869392403931/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (22/51)

def qb : ℚ := (67/153)

def rho : ℚ := (15772263500973326607013483269/62500000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (236943138534881287396793300189/1000000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell024Term01
