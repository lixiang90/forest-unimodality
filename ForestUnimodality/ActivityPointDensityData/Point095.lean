import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point095
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨95749/84875,28704059/100000000,1641873101993/13818650000000,8079092340131389/52511065725000000,3462264948616740385258917769/19676232924139018564500000000,1568107541413939243280942191/9543708036422999015637500000⟩
    path := ⟨22,71295941/42591882,4078130109618/2436257007625⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (28704059/100000000:ℝ)*S.card+(1568107541413939243280942191/9543708036422999015637500000:ℝ)≤hardCoreMean G S (95749/84875:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point095
