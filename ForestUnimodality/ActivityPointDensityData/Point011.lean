import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point011
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨64/89,61511441/250000000,2652017303/27125000000,315438617087/2687062500000,18919515834339511/139358226750000000,1252065324192259/10347009406250000⟩
    path := ⟨16,188488559/126977118,8126535552/5474518249⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (61511441/250000000:ℝ)*S.card+(1252065324192259/10347009406250000:ℝ)≤hardCoreMean G S (64/89:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point011
