import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point021
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨841/945,265848113/1000000000,142617007149/1313500000000,8710154041299/64519250000000,220931810425526883373/1415956751659000000000,118167936996247225077/837067890671375000000⟩
    path := ⟨18,734151887/468303774,131281157978/83742155595⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (265848113/1000000000:ℝ)*S.card+(118167936996247225077/837067890671375000000:ℝ)≤hardCoreMean G S (841/945:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point021
