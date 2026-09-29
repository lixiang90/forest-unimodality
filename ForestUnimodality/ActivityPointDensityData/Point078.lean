import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point078
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨23607/21125,286214743/1000000000,4047370678123/34169500000000,19681597863642163/128529014750000000,516003940855336211152243227/2943935101816647455000000000,58462915027579432205714707/357837805409396731375000000⟩
    path := ⟨20,713785257/427570514,10093657123998/6046286445875⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286214743/1000000000:ℝ)*S.card+(58462915027579432205714707/357837805409396731375000000:ℝ)≤hardCoreMean G S (23607/21125:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point078
