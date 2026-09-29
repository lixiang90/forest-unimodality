import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point048
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨10429/10175,139296539/500000000,891710505213/7758250000000,1953987042153641/13348172625000000,2236032819953642653675169/13268421867539444500000000,1210273819705340354757991/7813182912840545687500000⟩
    path := ⟨20,360703461/221406922,209913889958/128849298575⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (139296539/500000000:ℝ)*S.card+(1210273819705340354757991/7813182912840545687500000:ℝ)≤hardCoreMean G S (10429/10175:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point048
