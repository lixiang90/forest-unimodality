import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point090
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨11953/10625,286798371/1000000000,2049565450999/17265500000000,5039066310945001/32797367250000000,33716983392605558007362989/191833741993443855000000000,3818414988237195978805599/23278038529967741375000000⟩
    path := ⟨20,713201629/426403258,5096798142874/3047232691875⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286798371/1000000000:ℝ)*S.card+(3818414988237195978805599/23278038529967741375000000:ℝ)≤hardCoreMean G S (11953/10625:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point090
