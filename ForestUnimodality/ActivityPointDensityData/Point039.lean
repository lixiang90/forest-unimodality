import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point039
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨49/50,274582591/1000000000,2090444133/18500000000,696315727727/4875750000000,9153991899553499/55590051000000000,1233411014153309/8194387625000000⟩
    path := ⟨20,725417409/450834818,11045453041/6864564775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (274582591/1000000000:ℝ)*S.card+(1233411014153309/8194387625000000:ℝ)≤hardCoreMean G S (49/50:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point039
