import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point058
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨7339/6875,282195827/1000000000,1256833340669/10776500000000,1919674454501953/12833465250000000,5018794622005607849750173/29201182385648655000000000,570517288719057800130943/3590761679604311375000000⟩
    path := ⟨20,717804173/435608346,17859942186/10838526875⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (282195827/1000000000:ℝ)*S.card+(570517288719057800130943/3590761679604311375000000:ℝ)≤hardCoreMean G S (7339/6875:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point058
