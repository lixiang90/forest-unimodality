import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point097
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨31933/28275,143568723/500000000,2737934294057/23035250000000,1497357038400829/9726884625000000,71319452614054214702339201/405128088539646382500000000,96897700966825096451900167/589340499215158348187500000⟩
    path := ⟨22,356431277/212862554,6797339936882/4059405642825⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143568723/500000000:ℝ)*S.card+(96897700966825096451900167/589340499215158348187500000:ℝ)≤hardCoreMean G S (31933/28275:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point097
