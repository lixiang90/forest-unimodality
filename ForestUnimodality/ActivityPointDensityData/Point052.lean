import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point052
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨3579/3425,70077379/250000000,153121098043/1322875000000,114620436481051/774926937500000,45557564862537390504977/267757116733804250000000,8235744375643012600351/52525944253035343750000⟩
    path := ⟨20,179922621/109845242,393136121118/240015023075⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (70077379/250000000:ℝ)*S.card+(8235744375643012600351/52525944253035343750000:ℝ)≤hardCoreMean G S (3579/3425:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point052
