import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point049
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨5227/5075,139512439/500000000,447011334769/3882250000000,490368739453379/3341067375000000,140356353285726683950759/830842303863339500000000,76006292833457364580451/489174557981780687500000⟩
    path := ⟨20,360487561/220975122,1155036962694/708025627925⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (139512439/500000000:ℝ)*S.card+(76006292833457364580451/489174557981780687500000:ℝ)≤hardCoreMean G S (5227/5075:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point049
