import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point087
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨95549/85075,57330597/200000000,3276637034719/27617300000000,16105112865212087/104909241450000000,6893670548843759425482870527/39248632194807762129000000000,3123148375988193795371787153/19058536468960959731275000000⟩
    path := ⟨20,142669403/85338806,8154037574494/4877400539775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (57330597/200000000:ℝ)*S.card+(3123148375988193795371787153/19058536468960959731275000000:ℝ)≤hardCoreMean G S (95549/85075:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point087
