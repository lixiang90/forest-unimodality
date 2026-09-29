import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point020
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1677/1895,265334281/1000000000,284260359031/2624500000000,104015677213021/773114750000000,10545269718818048627663/67809409206437000000000,1879365093522364670269/13364151981181375000000⟩
    path := ⟨18,734665719/469331438,787068821526/502808462495⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (265334281/1000000000:ℝ)*S.card+(1879365093522364670269/13364151981181375000000:ℝ)≤hardCoreMean G S (1677/1895:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point020
