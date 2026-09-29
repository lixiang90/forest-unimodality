import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point054
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨10787/10225,28115287/100000000,184661988687/1589950000000,415696897853977/2796303225000000,496124651691940614705937/2902404898097150900000000,269334066341233739470643/1707594181973095137500000⟩
    path := ⟨22,71884713/43769426,472140798262/287478809575⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (28115287/100000000:ℝ)*S.card+(269334066341233739470643/1707594181973095137500000:ℝ)≤hardCoreMean G S (10787/10225:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point054
