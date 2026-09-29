import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point032
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨9237/9775,67825413/250000000,393249908163/3531125000000,778832110147173/5567842437500000,2255946302112318417310239/13972203563647894250000000,404025940510184350923657/2748941509461675343750000⟩
    path := ⟨20,182174587/114349174,20710653338/12999870825⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (67825413/250000000:ℝ)*S.card+(404025940510184350923657/2748941509461675343750000:ℝ)≤hardCoreMean G S (9237/9775:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point032
