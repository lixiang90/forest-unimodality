import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point084
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨47737/42575,286507559/1000000000,8184917987609/69024500000000,40213040581196957/262167269250000000,4301317544082153828202389893/24506085854934581565000000000,974454509262527015877823051/5952406366774224776375000000⟩
    path := ⟨20,713492441/426984882,20382977312034/12198059324425⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286507559/1000000000:ℝ)*S.card+(974454509262527015877823051/5952406366774224776375000000:ℝ)≤hardCoreMean G S (47737/42575:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point084
