import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point050
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨3493/3375,11178251/40000000,23902141389/207220000000,5833978963197/39645530000000,2227527517365134604991/13154105053572760000000,1206854603063569870599/7743597435443255000000⟩
    path := ⟨20,28821749/17643498,2934701834/1796504625⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (11178251/40000000:ℝ)*S.card+(1206854603063569870599/7743597435443255000000:ℝ)≤hardCoreMean G S (3493/3375:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point050
