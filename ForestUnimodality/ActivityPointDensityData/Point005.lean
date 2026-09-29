import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point005
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨19/32,227834473/1000000000,305158689/3500000000,115359327053/1134750000000,370126315733037/3160657000000000,244342384783267/2354202625000000⟩
    path := ⟨18,772165527/544331054,5171145013/3645351568⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (227834473/1000000000:ℝ)*S.card+(244342384783267/2354202625000000:ℝ)≤hardCoreMean G S (19/32:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point005
