import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point031
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨47/50,2166603/8000000,4000573/36000000,5167346219/37054000000,194684047423681/1209294344000000,8712952619057/59488781000000⟩
    path := ⟨18,5833397/3666794,86169659/54165075⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (2166603/8000000:ℝ)*S.card+(8712952619057/59488781000000:ℝ)≤hardCoreMean G S (47/50:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point031
