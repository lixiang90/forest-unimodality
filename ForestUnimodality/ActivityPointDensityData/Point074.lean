import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point074
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4657/4205,285428757/1000000000,798288634117/6759500000000,23978586878711/157300500000000,12307441447698891974077/70481224480695000000000,89298022393903248303633/549541934321966375000000⟩
    path := ⟨20,714571243/429142486,1998516557302/1200227923185⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (285428757/1000000000:ℝ)*S.card+(89298022393903248303633/549541934321966375000000:ℝ)≤hardCoreMean G S (4657/4205:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point074
