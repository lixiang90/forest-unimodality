import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell230Term00
open CoupledFlow


def environment : Environment := ⟨(107/49), (9/4), (32070604477092120709087568120869697656913/10000000000000000000000000000000000000000), (42070604477092120709087568120869697656913/10000000000000000000000000000000000000000), 15, (33756581557164709901001680960722553452251/10000000000000000000000000000000000000000), (14562901549762657168530312041839510727393/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (107/156)

def qb : ℚ := (9/13)

def rho : ℚ := (32911706447415606161303351683/100000000000000000000000000000)

def retention : ℚ := (9/10)

def rate : ℚ := (31991254456640213713180887577/500000000000000000000000000000)

def finish : ℚ := (2634012891445657530687524520982819957/25000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell230Term00
