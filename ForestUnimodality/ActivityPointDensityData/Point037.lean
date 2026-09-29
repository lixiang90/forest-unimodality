import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point037
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4777/4925,136827963/500000000,407367923723/3619750000000,207232809554209/1459544625000000,52267756248296638518989/319157617035988500000000,56289107276568124330767/376479890047768187500000⟩
    path := ⟨22,363172037/226344074,1081245641498/673877717775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (136827963/500000000:ℝ)*S.card+(56289107276568124330767/376479890047768187500000:ℝ)≤hardCoreMean G S (4777/4925:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point037
