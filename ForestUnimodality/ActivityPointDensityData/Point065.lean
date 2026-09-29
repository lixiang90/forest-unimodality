import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point065
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨11311/10425,283627867/1000000000,1937949879251/16523500000000,757521993823873/5021695250000000,4652047362197909779135193/26875311615872005000000000,3169047844157817840150703/19747316813802536375000000⟩
    path := ⟨22,716372133/432744266,4894770392726/2956820513475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (283627867/1000000000:ℝ)*S.card+(3169047844157817840150703/19747316813802536375000000:ℝ)≤hardCoreMean G S (11311/10425:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point065
