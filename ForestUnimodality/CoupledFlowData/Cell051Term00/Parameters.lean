import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell051Term00
open CoupledFlow


def environment : Environment := ⟨(4487/4825), (8999/9625), (25569219855886680502260360606229296161601/10000000000000000000000000000000000000000), (35569219855886680502260360606229296161601/10000000000000000000000000000000000000000), 4, (12485221448432837593595201808741891566499/10000000000000000000000000000000000000000), (1718682396279661929981964052273719051537/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (4487/9312)

def qb : ℚ := (8999/18624)

def rho : ℚ := (16980753671294274694327282849/62500000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (22955188320621994893367190557/250000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell051Term00
