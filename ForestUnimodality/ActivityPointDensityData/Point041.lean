import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point041
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨197/199,275488823/1000000000,33635127961/296500000000,280814415317/1955250000000,118266952980301933/714398817000000000,1594995862905010943/10527714944875000000⟩
    path := ⟨20,724511177/449022354,88457403738/54822275777⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (275488823/1000000000:ℝ)*S.card+(1594995862905010943/10527714944875000000:ℝ)≤hardCoreMean G S (197/199:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point041
