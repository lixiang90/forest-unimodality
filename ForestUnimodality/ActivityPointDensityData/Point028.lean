import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point028
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨2983/3225,269363393/1000000000,507281054937/4595500000000,6797263002241/49203250000000,2093683717441516579953/13123078123139000000000,17967813764054251119597/124002061303946375000000⟩
    path := ⟨18,730636607/461273214,458659332454/289565647475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (269363393/1000000000:ℝ)*S.card+(17967813764054251119597/124002061303946375000000:ℝ)≤hardCoreMean G S (2983/3225:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point028
