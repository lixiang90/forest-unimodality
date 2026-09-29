import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell026Term00
open CoupledFlow


def environment : Environment := ⟨(4/5), (301/365), (6280487004534573856485272513246237038901/2500000000000000000000000000000000000000), (8780487004534573856485272513246237038901/2500000000000000000000000000000000000000), 2, (5628921194322119354837906915685806323359/5000000000000000000000000000000000000000), (7936716481576296488895096175636989035163/5000000000000000000000000000000000000000)⟩

def qa : ℚ := (4/9)

def qb : ℚ := (301/666)

def rho : ℚ := (128680775826712959996845876723/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (19193300910222735250729899277/125000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell026Term00
