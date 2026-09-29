import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell179Term00
open CoupledFlow


def environment : Environment := ⟨(31883/28325), (47837/42475), (2666612296695415552992993810474476742643/1000000000000000000000000000000000000000), (3666612296695415552992993810474476742643/1000000000000000000000000000000000000000), 10, (232073776582386322426507399504407924393/156250000000000000000000000000000000000), (77686124739577727791888495398913785073/40000000000000000000000000000000000000)⟩

def qa : ℚ := (31883/60208)

def qb : ℚ := (47837/90312)

def rho : ℚ := (288923908305008512293403771479/1000000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (100965645181672685162168902061/1000000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell179Term00
