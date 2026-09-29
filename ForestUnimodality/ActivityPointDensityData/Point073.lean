import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point073
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨2326/2105,71307667/250000000,99674094081/844625000000,383007513091409/2515423312500000,98232896733913773797909/563088123589503750000000,1392289188397965727133/8579909377987531250000⟩
    path := ⟨20,178692333/107384666,249776733116/150102639035⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (71307667/250000000:ℝ)*S.card+(1392289188397965727133/8579909377987531250000:ℝ)≤hardCoreMean G S (2326/2105:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point073
