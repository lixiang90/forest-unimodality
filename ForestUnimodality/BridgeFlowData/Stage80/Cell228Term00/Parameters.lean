import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell228Term00
open CoupledFlow


def environment : Environment := ⟨(41/22), (83/43), (31153148195259458596588234306047918182873/10000000000000000000000000000000000000000), (41153148195259458596588234306047918182873/10000000000000000000000000000000000000000), 15, (32905463606175910943602572022763863200327/10000000000000000000000000000000000000000), (27108819842909008440609709900015692136337/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (41/63)

def qb : ℚ := (83/126)

def rho : ℚ := (320135973852926091373635073559/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (17700070439509760042206000723/100000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell228Term00
