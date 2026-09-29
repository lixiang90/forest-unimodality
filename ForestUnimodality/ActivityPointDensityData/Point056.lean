import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point056
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨21967/20675,56356271/200000000,752277686961/6460900000000,860739606479699/5768396550000000,20226351189107541243200231/117930014974204209000000000,9200395821272490242285059/58074390139398269275000000⟩
    path := ⟨20,143643729/87287458,1917443589886/1165165902925⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (56356271/200000000:ℝ)*S.card+(9200395821272490242285059/58074390139398269275000000:ℝ)≤hardCoreMean G S (21967/20675:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point056
