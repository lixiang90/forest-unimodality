import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point029
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4487/4825,67462823/250000000,190830505423/1724875000000,11522378406313/83144156250000,5327278092566759359081/33290047259718250000000,22868668184258052236347/157258823759256593750000⟩
    path := ⟨18,182537177/115074354,516338626398/325508120975⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (67462823/250000000:ℝ)*S.card+(22868668184258052236347/157258823759256593750000:ℝ)≤hardCoreMean G S (4487/4825:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point029
