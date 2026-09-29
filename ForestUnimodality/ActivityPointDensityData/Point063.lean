import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point063
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨27/25,283222507/1000000000,4625421947/39500000000,25922192677/172250000000,909951413159493/5267405000000000,103347716587063/645811375000000⟩
    path := ⟨20,716777493/433554986,11705984622/7080562675⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (283222507/1000000000:ℝ)*S.card+(103347716587063/645811375000000:ℝ)≤hardCoreMean G S (27/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point063
