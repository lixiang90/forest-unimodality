import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point059
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨107/100,28240293/100000000,916273999/7850000000,326293185929/2178675000000,90519331895057683/526128225750000000,2572004575403307/16164435012500000⟩
    path := ⟨22,71759707/43519414,2328288649/1412014650⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (28240293/100000000:ℝ)*S.card+(2572004575403307/16164435012500000:ℝ)≤hardCoreMean G S (107/100:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point059
