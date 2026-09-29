import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point046
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨407/401,277719601/1000000000,13914136957/121500000000,2981741012489/20477750000000,15726406664147760779/93782115497000000000,28346060010990723649/184134282093875000000⟩
    path := ⟨20,722280399/444560798,180936244786/111365560001⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (277719601/1000000000:ℝ)*S.card+(28346060010990723649/184134282093875000000:ℝ)≤hardCoreMean G S (407/401:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point046
