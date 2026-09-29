import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point077
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨11791/10575,286018827/1000000000,2021454926161/17078500000000,1637397068876311/10704926750000000,10725727680714747356336211/61250086284580585000000000,3646206146917576817327303/22347701087656601375000000⟩
    path := ⟨22,713981173/427962346,5046104021686/3024649095525⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286018827/1000000000:ℝ)*S.card+(3646206146917576817327303/22347701087656601375000000:ℝ)≤hardCoreMean G S (11791/10575:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point077
