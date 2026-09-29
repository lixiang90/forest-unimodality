import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01
open CoupledFlow


def environment : Environment := ⟨(53/50), (21967/20675), (13191060322916795193611531981031208900291/5000000000000000000000000000000000000000), (18191060322916795193611531981031208900291/5000000000000000000000000000000000000000), 9, (1428235360632912230973676393359416582349/1000000000000000000000000000000000000000), (18742227011561992402704588106904580737897/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (53/103)

def qb : ℚ := (21967/42642)

def rho : ℚ := (283188211183164168448876073019/1000000000000000000000000000000)

def retention : ℚ := (1/10)

def rate : ℚ := (265589076835763743921124742449/1000000000000000000000000000000)

def finish : ℚ := (11160864579549677/5000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell099Term01
