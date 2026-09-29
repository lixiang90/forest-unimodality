import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point102
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨32351/28425,287809059/1000000000,5548205762507/46563500000000,6137738229713401/39719015250000000,298488335147613536435078321/1690251035751332805000000000,202669723391881921061184791/1226999517293341856375000000⟩
    path := ⟨22,712190941/424381882,13729178264582/8180972502075⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287809059/1000000000:ℝ)*S.card+(202669723391881921061184791/1226999517293341856375000000:ℝ)≤hardCoreMean G S (32351/28425:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point102
