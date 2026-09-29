import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point089
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨95599/85025,143374957/500000000,8196039252589/69055750000000,40295946377406497/262343659875000000,17253453849656036137175776037/98186437612293043447500000000,7816031797570370797055674793/47664396609750788953187500000⟩
    path := ⟨22,356625043/213250086,20386494971514/12190455718925⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143374957/500000000:ℝ)*S.card+(7816031797570370797055674793/47664396609750788953187500000:ℝ)≤hardCoreMean G S (95599/85025:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point089
