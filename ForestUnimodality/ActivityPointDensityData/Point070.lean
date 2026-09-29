import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point070
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1531/1395,284634037/1000000000,262386097091/2228500000000,27693559030631/182509250000000,3091534770613421952331/17772425898535000000000,1052123642644343281753/6510477124541375000000⟩
    path := ⟨20,715365963/430731926,659450578706/397064481615⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (284634037/1000000000:ℝ)*S.card+(1052123642644343281753/6510477124541375000000:ℝ)≤hardCoreMean G S (1531/1395:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point070
