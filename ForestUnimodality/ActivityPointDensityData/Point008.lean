import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point008
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨101/154,237328311/1000000000,4127780321/44500000000,639689055523/5826750000000,52368187678169831/413054423000000000,172954852861226121/1535946536125000000⟩
    path := ⟨16,762671689/525343378,3789977227/2610611421⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (237328311/1000000000:ℝ)*S.card+(172954852861226121/1535946536125000000:ℝ)≤hardCoreMean G S (101/154:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point008
