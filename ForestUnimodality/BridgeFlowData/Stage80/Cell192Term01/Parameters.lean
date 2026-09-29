import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage80.Cell192Term01
open CoupledFlow


def environment : Environment := ⟨(6/5), (97/80), (27396964819754993759484605572508110778021/10000000000000000000000000000000000000000), (37396964819754993759484605572508110778021/10000000000000000000000000000000000000000), 13, (2124584154010707075519800438430036181467/1250000000000000000000000000000000000000), (2049438185037420561960455785612026409869/1000000000000000000000000000000000000000)⟩

def qa : ℚ := (6/11)

def qb : ℚ := (97/177)

def rho : ℚ := (293083998400085596895936799881/1000000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (10823979476430743210348768761/62500000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage80.Cell192Term01
