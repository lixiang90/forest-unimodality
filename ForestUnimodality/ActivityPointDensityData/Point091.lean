import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point091
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨31883/28325,35855853/125000000,683373641377/5755687500000,140031648910379/911160472656250,53310920317561277039200783/303244816893543068125000000,24148755332742053175256937/147168050190744024546875000⟩
    path := ⟨20,89144147/53288294,1698990677602/1015617036225⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (35855853/125000000:ℝ)*S.card+(24148755332742053175256937/147168050190744024546875000:ℝ)≤hardCoreMean G S (31883/28325:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point091
