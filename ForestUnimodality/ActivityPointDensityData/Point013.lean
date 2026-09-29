import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point013
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨22/29,62767667/250000000,917960309/9125000000,7378130677/60562500000,49634167150073/352150750000000,82262592012737/652962156250000⟩
    path := ⟨16,187232333/124464666,2738222652/1820262343⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (62767667/250000000:ℝ)*S.card+(82262592012737/652962156250000:ℝ)≤hardCoreMean G S (22/29:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point013
