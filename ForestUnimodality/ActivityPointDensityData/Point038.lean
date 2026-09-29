import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point038
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨3193/3275,54823901/200000000,108946292439/966100000000,73993569137441/519622950000000,8299344691464693349041/50538128353743800000000,4470966511198349865649/29803161501386275000000⟩
    path := ⟨20,145176099/90352198,288494568214/179548275775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (54823901/200000000:ℝ)*S.card+(4470966511198349865649/29803161501386275000000:ℝ)≤hardCoreMean G S (3193/3275:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point038
