import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.BridgeFlowData.Stage99.Cell187Term01
open CoupledFlow


def environment : Environment := ⟨(107/49), (9/4), (6518046568188002087138450320960470817859/2000000000000000000000000000000000000000), (8518046568188002087138450320960470817859/2000000000000000000000000000000000000000), 15, (34238462188230371644311612200521879955759/10000000000000000000000000000000000000000), (5897109162591693752634311760664941335441/2000000000000000000000000000000000000000)⟩

def qa : ℚ := (107/156)

def qb : ℚ := (9/13)

def rho : ℚ := (162550811800730310764371562661/500000000000000000000000000000)

def retention : ℚ := (3/5)

def rate : ℚ := (160150182347815547121534861391/1000000000000000000000000000000)

def finish : ℚ := (10216512475319813664110281926073238697/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.BridgeFlowData.Stage99.Cell187Term01
