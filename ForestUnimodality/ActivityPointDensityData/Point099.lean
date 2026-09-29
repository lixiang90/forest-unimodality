import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point099
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨8069/7125,287377697/1000000000,1383732634689/11631500000000,764424898811401/4958941750000000,2320432271151198197351781/13166338563139685000000000,788019889311527720389413/4784922099000671375000000⟩
    path := ⟨20,712622303/425244606,1143766241938/682522030375⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287377697/1000000000:ℝ)*S.card+(788019889311527720389413/4784922099000671375000000:ℝ)≤hardCoreMean G S (8069/7125:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point099
