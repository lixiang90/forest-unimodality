import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point069
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨2294/2095,35554217/125000000,49141167789/417687500000,186609965826499/1231251656250000,46842864502321081770439/269549823466914375000000,664348482971340287143/4116658395123765625000⟩
    path := ⟨20,89445783/53891566,123627252404/74486084615⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (35554217/125000000:ℝ)*S.card+(664348482971340287143/4116658395123765625000:ℝ)≤hardCoreMean G S (2294/2095:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point069
