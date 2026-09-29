import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point060
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨7427/6925,282607953/1000000000,1272081391613/10889500000000,491038868544877/3274722750000000,1310519559117281999647093/7609370362386195000000000,595684325476424383667277/3738374345944136375000000⟩
    path := ⟨20,717392047/434784094,3229141466138/1957060074525⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (282607953/1000000000:ℝ)*S.card+(595684325476424383667277/3738374345944136375000000:ℝ)≤hardCoreMean G S (7427/6925:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point060
