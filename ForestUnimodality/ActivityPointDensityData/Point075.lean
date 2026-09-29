import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point075
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨111/100,17851673/62500000,594630647/5031250000,217861349701/1427546875000,63429283490028783/362896691093750000,1797446660369207/11046417507812500⟩
    path := ⟨20,44648327/26796654,1487214297/892583650⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (17851673/62500000:ℝ)*S.card+(1797446660369207/11046417507812500:ℝ)≤hardCoreMean G S (111/100:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point075
