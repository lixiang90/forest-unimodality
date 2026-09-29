import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point081
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨94503/84425,8948801/31250000,506339143769/4272359375000,9853113354404081/64290717531250000,258440585827755432854013699/1473442703893641388632812500,468445600956188676713939969/2864349368277182030199218750⟩
    path := ⟨22,22301199/13352398,1261841668194/755502524425⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (8948801/31250000:ℝ)*S.card+(468445600956188676713939969/2864349368277182030199218750:ℝ)≤hardCoreMean G S (94503/84425:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point081
