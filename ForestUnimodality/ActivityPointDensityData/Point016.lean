import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point016
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨301/365,64710043/250000000,12675388419/120875000000,849346275877/6597562500000,987632112243167033/6631755467250000000,525793316765630567/3927749897843750000⟩
    path := ⟨18,185289957/120579914,36294554114/23619165695⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (64710043/250000000:ℝ)*S.card+(525793316765630567/3927749897843750000:ℝ)≤hardCoreMean G S (301/365:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point016
