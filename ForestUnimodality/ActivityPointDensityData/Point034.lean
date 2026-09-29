import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point034
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨9287/9725,68063149/250000000,395630946449/3537375000000,785656202351779/5582695562500000,2278602344951617921428097/14031249201144631750000000,408439627847596729258961/2759757458009175343750000⟩
    path := ⟨18,181936851/113873702,1057545070474/661914124025⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (68063149/250000000:ℝ)*S.card+(408439627847596729258961/2759757458009175343750000:ℝ)≤hardCoreMean G S (9287/9725:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point034
