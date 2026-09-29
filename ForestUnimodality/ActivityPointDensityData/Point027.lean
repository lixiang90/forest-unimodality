import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point027
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨23/25,134437459/500000000,1954940411/17750000000,2427130781/17625000000,14887779706201/93600500000000,31928273757431/221143187500000⟩
    path := ⟨20,365562541/231125082,5315876886/3360936475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (134437459/500000000:ℝ)*S.card+(31928273757431/221143187500000:ℝ)≤hardCoreMean G S (23/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point027
