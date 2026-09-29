import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point015
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4/5,256024981/1000000000,671675247/6500000000,4828177907/38250000000,1020397074043/6987000000000,67800553679/517625000000⟩
    path := ⟨18,743975019/487950038,1951800152/1280124905⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (256024981/1000000000:ℝ)*S.card+(67800553679/517625000000:ℝ)≤hardCoreMean G S (4/5:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point015
