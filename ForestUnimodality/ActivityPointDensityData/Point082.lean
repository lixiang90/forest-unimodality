import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point082
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨28/25,57282117/200000000,960148523/8100000000,44281210091/288850000000,1630747132413899/9295193000000000,23091855778223/141149525000000⟩
    path := ⟨20,142717883/85435766,2392201448/1432052925⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (57282117/200000000:ℝ)*S.card+(23091855778223/141149525000000:ℝ)≤hardCoreMean G S (28/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point082
