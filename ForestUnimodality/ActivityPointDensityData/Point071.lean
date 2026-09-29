import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point071
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨11/10,142417129/500000000,29457871/250000000,17147332513/112875000000,49331077272419/283316250000000,1398818642171/8643812500000⟩
    path := ⟨20,357582871/215165742,1183411581/712085645⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (142417129/500000000:ℝ)*S.card+(1398818642171/8643812500000:ℝ)≤hardCoreMean G S (11/10:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point071
