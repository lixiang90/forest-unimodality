import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage130.Cell047Term00
open CoupledFlow


def environment : Environment := ⟨(47/50), (9237/9775), (7217020828950136755733221123500946770461/2500000000000000000000000000000000000000), (9717020828950136755733221123500946770461/2500000000000000000000000000000000000000), 4, (13867746002102566638168821030342211414697/10000000000000000000000000000000000000000), (3776819751610032114988755039670870831843/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (47/97)

def qb : ℚ := (9237/19012)

def rho : ℚ := (1/4)

def retention : ℚ := (3/5)

def rate : ℚ := (9684069966728355732603336277/62500000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage130.Cell047Term00
