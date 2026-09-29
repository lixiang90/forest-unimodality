import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point068
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4583/4195,56846671/200000000,157071628769/1336100000000,74515393730383/492226350000000,74772995354463509946907/430689973893333000000000,16970274878463987715379/105303146217911275000000⟩
    path := ⟨20,143153329/86306658,395543413614/238471784845⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (56846671/200000000:ℝ)*S.card+(16970274878463987715379/105303146217911275000000:ℝ)≤hardCoreMean G S (4583/4195:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point068
