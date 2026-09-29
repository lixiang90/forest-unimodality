import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point001
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨29/56,107350649/500000000,1131013007/14250000000,27580572281/303875000000,2929117063/28500000000,788221798311539/8550899312500000⟩
    path := ⟨14,392649351/285298702,4136831179/3005818172⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (107350649/500000000:ℝ)*S.card+(788221798311539/8550899312500000:ℝ)≤hardCoreMean G S (29/56:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point001
