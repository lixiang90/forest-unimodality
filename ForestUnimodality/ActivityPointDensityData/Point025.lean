import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point025
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨869/955,66968897/250000000,36902760379/336625000000,54254206961/396550781250,7677843870933117079/48575266938250000000,32904715275655537693/229597105454093750000⟩
    path := ⟨18,183031103/116062206,100858057014/63955296635⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (66968897/250000000:ℝ)*S.card+(32904715275655537693/229597105454093750000:ℝ)≤hardCoreMean G S (869/955:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point025
