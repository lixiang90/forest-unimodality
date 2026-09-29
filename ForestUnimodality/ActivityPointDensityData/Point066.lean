import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point066
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨22647/20825,283830421/1000000000,3880416393901/33059500000000,4553086537689769/30147152750000000,111915148081189795354925241/645900642794544995000000000,50816930293332487158506449/316210351568342566375000000⟩
    path := ⟨20,716169579/432339158,9791184911226/5910768517325⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (283830421/1000000000:ℝ)*S.card+(50816930293332487158506449/316210351568342566375000000:ℝ)≤hardCoreMean G S (22647/20825:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point066
