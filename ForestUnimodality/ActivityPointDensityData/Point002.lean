import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point002
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨89/166,218039159/1000000000,1749316163/21500000000,516141251803/5520750000000,14991682708994619019/140108236099000000000,133735856272898729/1406766596125000000⟩
    path := ⟨14,781960841/563921682,25094514849/18097250197⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (218039159/1000000000:ℝ)*S.card+(133735856272898729/1406766596125000000:ℝ)≤hardCoreMean G S (89/166:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point002
