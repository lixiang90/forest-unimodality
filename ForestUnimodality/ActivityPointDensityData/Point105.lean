import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point105
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨57/50,287952767/1000000000,2443936553/20500000000,914280918751/5911750000000,68938166775582777/390116382500000000,1950136275417533/11794887625000000⟩
    path := ⟨20,712047233/424094466,12086692281/7198819175⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287952767/1000000000:ℝ)*S.card+(1950136275417533/11794887625000000:ℝ)≤hardCoreMean G S (57/50:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point105
