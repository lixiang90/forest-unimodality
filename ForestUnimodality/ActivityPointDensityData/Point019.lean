import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point019
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨22/25,132409891/500000000,1863717521/17250000000,71682896193/534625000000,1257217663672839/8111330500000000,27996907337229/199855062500000⟩
    path := ⟨18,367590109/235180218,5173964796/3310247275⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (132409891/500000000:ℝ)*S.card+(27996907337229/199855062500000:ℝ)≤hardCoreMean G S (22/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point019
