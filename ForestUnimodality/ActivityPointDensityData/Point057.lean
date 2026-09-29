import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point057
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨10996/10325,70497159/250000000,470743312597/4039625000000,8622963250159793/57717279562500000,50690535574594800821372873/295243325296289741250000000,720420079893365084761221/4540810490577099406250000⟩
    path := ⟨20,179502841/109005682,1198626479272/727883166675⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (70497159/250000000:ℝ)*S.card+(720420079893365084761221/4540810490577099406250000:ℝ)≤hardCoreMean G S (10996/10325:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point057
