import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point007
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨33/52,234195233/1000000000,2682481253/29500000000,68720836889/641750000000,266140640234513/2153713000000000,2050225295405563/18696748625000000⟩
    path := ⟨16,765804767/531609534,8771557311/6089076058⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (234195233/1000000000:ℝ)*S.card+(2050225295405563/18696748625000000:ℝ)≤hardCoreMean G S (33/52:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point007
