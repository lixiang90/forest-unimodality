import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point088
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨15929/14175,71675363/250000000,682818015021/5754125000000,372957070400637/2428781312500000,4435137382154990723887657/25245371864179051250000000,3013869912328406749354647/18385559168133929093750000⟩
    path := ⟨20,178324637/106649274,566272095182/338666090175⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (71675363/250000000:ℝ)*S.card+(3013869912328406749354647/18385559168133929093750000:ℝ)≤hardCoreMean G S (15929/14175:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point088
