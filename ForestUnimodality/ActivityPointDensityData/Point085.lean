import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point085
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨31833/28375,286556039/1000000000,5458095614401/46020500000000,8939915584300691/58267232750000000,425059356535944498405899379/2421154303542065795000000000,192585515591145063047376731/1176006961894484446375000000⟩
    path := ⟨20,713443961/426887922,13589123221026/8131027606625⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286556039/1000000000:ℝ)*S.card+(192585515591145063047376731/1176006961894484446375000000:ℝ)≤hardCoreMean G S (31833/28375:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point085
