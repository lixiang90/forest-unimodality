import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point047
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨51/50,34770109/125000000,136242929/1187500000,93545955173/640718750000,3856532790479903/22940294125000000,173864780636791/1125873453125000⟩
    path := ⟨20,90229891/55459782,1414224441/869252725⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (34770109/125000000:ℝ)*S.card+(173864780636791/1125873453125000:ℝ)≤hardCoreMean G S (51/50:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point047
