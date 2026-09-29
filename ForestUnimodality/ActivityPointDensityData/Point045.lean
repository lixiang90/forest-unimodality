import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point045
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨203/201,277277901/1000000000,34692314093/303500000000,99000663973/681750000000,130470582407153431/780006537000000000,1762901865797671141/11487825344875000000⟩
    path := ⟨20,722722099/445444198,90425172194/55732858101⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (277277901/1000000000:ℝ)*S.card+(1762901865797671141/11487825344875000000:ℝ)≤hardCoreMean G S (203/201:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point045
