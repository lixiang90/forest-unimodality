import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point017
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨17/20,16352147/62500000,89742031/843750000,5386659831/41046875000,29130304359369/191935187500000,1294570420893/9466257812500⟩
    path := ⟨18,46147853/29795706,14897853/9618910⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (16352147/62500000:ℝ)*S.card+(1294570420893/9466257812500:ℝ)≤hardCoreMean G S (17/20:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point017
