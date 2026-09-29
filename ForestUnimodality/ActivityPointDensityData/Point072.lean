import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point072
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1549/1405,142516251/500000000,132749321747/1125750000000,42484197624049/279337625000000,4839822899987692610509/27769238225627500000000,548859091537396395239/3386952401625687500000⟩
    path := ⟨20,357483749/214967498,332984654402/200235332655⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (142516251/500000000:ℝ)*S.card+(548859091537396395239/3386952401625687500000:ℝ)≤hardCoreMean G S (1549/1405:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point072
