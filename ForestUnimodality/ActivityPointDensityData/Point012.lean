import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point012
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨65/88,248567323/1000000000,5406161793/54500000000,1294783481423/10824750000000,39015519218637407/281977521000000000,25841039323249177/209251812625000000⟩
    path := ⟨16,751432677/502865354,16343124005/10936962212⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (248567323/1000000000:ℝ)*S.card+(25841039323249177/209251812625000000:ℝ)≤hardCoreMean G S (65/88:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point012
