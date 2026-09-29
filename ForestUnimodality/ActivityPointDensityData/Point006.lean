import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point006
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨97/158,231031001/1000000000,489908989/5500000000,597521108101/5724750000000,48266020405071733/401060719000000000,159321147736748711/1492911536125000000⟩
    path := ⟨16,768968999/537937998,26089992903/18251449079⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (231031001/1000000000:ℝ)*S.card+(159321147736748711/1492911536125000000:ℝ)≤hardCoreMean G S (97/158:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point006
