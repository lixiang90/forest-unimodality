import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point042
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨395/397,137970621/500000000,33728872873/296750000000,1409799265111/9788625000000,2376303884743870343/14316438328500000000,12825115612987126269/84377142431937500000⟩
    path := ⟨20,362029379/224058758,88503209410/54774336537⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (137970621/500000000:ℝ)*S.card+(12825115612987126269/84377142431937500000:ℝ)≤hardCoreMean G S (395/397:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point042
