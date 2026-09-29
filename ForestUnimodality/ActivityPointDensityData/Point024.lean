import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point024
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1733/1915,267375003/1000000000,294255108857/2690500000000,6912083173003/50687250000000,244366133559096513553/1550934084889000000000,2093705902443137607087/14663473594496375000000⟩
    path := ⟨18,732624997/465249994,806278239602/512023130745⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (267375003/1000000000:ℝ)*S.card+(2093705902443137607087/14663473594496375000000:ℝ)≤hardCoreMean G S (1733/1915:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point024
