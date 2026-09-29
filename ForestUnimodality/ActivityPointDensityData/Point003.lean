import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point003
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨91/164,44267957/200000000,1441643439/17300000000,107220042341/1114350000000,284087125911331327/2570286905800000000,27984205363042247/285659775725000000⟩
    path := ⟨14,155732043/111464086,5071615913/3629972474⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (44267957/200000000:ℝ)*S.card+(27984205363042247/285659775725000000:ℝ)≤hardCoreMean G S (91/164:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point003
