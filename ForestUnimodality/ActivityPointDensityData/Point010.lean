import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point010
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨7/10,243505411/1000000000,144483767/1500000000,15172648403/131750000000,16769478039697/125953000000000,739336485689/6237625000000⟩
    path := ⟨16,756494589/512989178,1795462123/1217527055⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (243505411/1000000000:ℝ)*S.card+(739336485689/6237625000000:ℝ)≤hardCoreMean G S (7/10:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point010
