import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point040
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨131/133,13751797/50000000,223608037/1975000000,15537216337/108487500000,2906639968507541/17604338950000000,15672804355398613/103785409193750000⟩
    path := ⟨20,36248203/22496406,2947029186/1828989001⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (13751797/50000000:ℝ)*S.card+(15672804355398613/103785409193750000:ℝ)≤hardCoreMean G S (131/133:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point040
