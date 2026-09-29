import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point022
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1687/1885,266361283/1000000000,286206012703/2629500000000,105028609377913/775347250000000,10664248860447496353019/68122452883627000000000,1902041143804448793887/13422002088001375000000⟩
    path := ⟨18,733638717/467277434,60638233166/38622386035⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (266361283/1000000000:ℝ)*S.card+(1902041143804448793887/13422002088001375000000:ℝ)≤hardCoreMean G S (1687/1885:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point022
