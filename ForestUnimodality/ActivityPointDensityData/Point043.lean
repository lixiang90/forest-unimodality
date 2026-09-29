import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point043
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1,138196601/500000000,85410197/750000000,18053399/125000000,582468521/3500000000,104837389/687500000⟩
    path := ⟨20,361803399/223606798,223606798/138196601⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (138196601/500000000:ℝ)*S.card+(104837389/687500000:ℝ)≤hardCoreMean G S (1:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point043
