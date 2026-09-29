import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point051
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨26/25,279887273/1000000000,4448679979/38500000000,193752154931/1313250000000,59148399213353/348449000000000,92178475917127/589650125000000⟩
    path := ⟨20,720112727/440225454,11445861804/6997181825⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (279887273/1000000000:ℝ)*S.card+(92178475917127/589650125000000:ℝ)≤hardCoreMean G S (26/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point051
