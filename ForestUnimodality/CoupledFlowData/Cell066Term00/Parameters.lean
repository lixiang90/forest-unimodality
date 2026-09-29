import ForestUnimodality.CoupledFlowRow

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.CoupledFlowData.Cell066Term00
open CoupledFlow


def environment : Environment := ⟨(24/25), (9529/9875), (25766316554539988468133291444183377845371/10000000000000000000000000000000000000000), (35766316554539988468133291444183377845371/10000000000000000000000000000000000000000), 5, (12962571116098584563058329114484604638311/10000000000000000000000000000000000000000), (17564276976304450119194090608721057899843/10000000000000000000000000000000000000000)⟩

def qa : ℚ := (24/49)

def qb : ℚ := (9529/19404)

def rho : ℚ := (137303574933144262173784011173/500000000000000000000000000000)

def retention : ℚ := (4/5)

def rate : ℚ := (4687005562689058065593259963/50000000000000000000000000000)

def finish : ℚ := (4462871026284195115325901806196690067/20000000000000000000000000000000000000)

theorem environment_checked : environment.check=true := by decide +kernel

theorem normalization_checked : 0<rho ∧ rho≤qa ∧ qa≤qb ∧ qb<1 ∧
    environment.a≤qa/(1-qa) ∧ qb/(1-qb)≤environment.b ∧
    2*qb/rho-1≤environment.beta ∧ 2*qb/rho≤environment.gamma := by decide +kernel

#print axioms environment_checked

#print axioms normalization_checked

end ForestUnimodality.CoupledFlowData.Cell066Term00
