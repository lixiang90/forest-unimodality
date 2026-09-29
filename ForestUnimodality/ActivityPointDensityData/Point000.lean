import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point000
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1/2,42264973/200000000,7735027/100000000,13205081/150000000,19615243/200000000,466620643/5225000000⟩
    path := ⟨14,157735027/115470054,57735027/42264973⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (42264973/200000000:ℝ)*S.card+(466620643/5225000000:ℝ)≤hardCoreMean G S (1/2:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point000
