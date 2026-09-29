import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point055
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨53/50,56314797/200000000,453722917/3900000000,160411364981/1076350000000,6903565430628619/40294238600000000,312474533092343/1975259525000000⟩
    path := ⟨20,143685203/87370406,2315315759/1407869925⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (56314797/200000000:ℝ)*S.card+(312474533092343/1975259525000000:ℝ)≤hardCoreMean G S (53/50:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point055
