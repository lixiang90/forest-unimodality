import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point036
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨9529/9875,273191849/1000000000,1624740232883/14466500000000,3301751436674731/23322395250000000,3329046461813631354738779/20384233894775289000000000,1791784630301820766701181/12024415978640441375000000⟩
    path := ⟨18,726808151/453616302,4322509741758/2697769508875⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (273191849/1000000000:ℝ)*S.card+(1791784630301820766701181/12024415978640441375000000:ℝ)≤hardCoreMean G S (9529/9875:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point036
