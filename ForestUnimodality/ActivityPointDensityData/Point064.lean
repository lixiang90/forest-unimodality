import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point064
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨22597/20875,283425229/1000000000,3871378545199/33034500000000,4537179520517731/30113190250000000,111383327575732669760833659/644115062003443745000000000,50592713255929355095401401/315703683297492316375000000⟩
    path := ⟨22,716574771/433149542,9787880200574/5916501655375⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (283425229/1000000000:ℝ)*S.card+(50592713255929355095401401/315703683297492316375000000:ℝ)≤hardCoreMean G S (22597/20875:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point064
