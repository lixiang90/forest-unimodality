import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell168Term01
open CoupledFlow


def environment : Environment := ⟨(12116/10675), (24257/21325), (1674731422722361575688702839243768005057/625000000000000000000000000000000000000), (2299731422722361575688702839243768005057/625000000000000000000000000000000000000), 10, (932190674017830035655769636411152517337/625000000000000000000000000000000000000), (19581268086868088189717297098516460181183/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (12116/22791)

def qb : ℚ := (24257/45582)

def rho : ℚ := (144626078126884954993027482873/500000000000000000000000000000)

def retention : ℚ := (1/20)

def rate : ℚ := (11228234043306441826085540599/40000000000000000000000000000)

def finish : ℚ := (59914645471079819868704471522850815513/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell168Term01
