import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point080
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨47239/42225,143156337/500000000,4049599263089/34175750000000,6566005494692153/42854653875000000,688784939754293997154095673/3927869031704404627500000000,468198108753008036557343533/2863800450816583468187500000⟩
    path := ⟨24,356843663/213687326,10094375592914/6044776329825⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143156337/500000000:ℝ)*S.card+(468198108753008036557343533/2863800450816583468187500000:ℝ)≤hardCoreMean G S (47239/42225:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point080
