import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point076
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨23557/21175,57164567/200000000,807688884137/6828900000000,3923187879656597/25677845450000000,102733342119404836140866613/587215271796958741000000000,11643159964284970327618483/71457702985187646275000000⟩
    path := ⟨20,142835433/85670866,2018148590362/1210459706225⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (57164567/200000000:ℝ)*S.card+(11643159964284970327618483/71457702985187646275000000:ℝ)≤hardCoreMean G S (23557/21175:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point076
