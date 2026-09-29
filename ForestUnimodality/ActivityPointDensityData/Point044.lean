import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point044
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨405/403,276835769/1000000000,69198212203/606500000000,2958307400779/20427250000000,15586549855031239481/93419452171000000000,28067115459522083641/183475879263875000000⟩
    path := ⟨20,723164231/446328462,180763027110/111564814907⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (276835769/1000000000:ℝ)*S.card+(28067115459522083641/183475879263875000000:ℝ)≤hardCoreMean G S (405/403:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point044
