import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point004
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨31/54,28075559/125000000,154558789/1812500000,2575559353/26031250000,68365882533183/600488875000000,225690079485769/2237403265625000⟩
    path := ⟨16,96924441/68848882,1067157671/758040093⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (28075559/125000000:ℝ)*S.card+(225690079485769/2237403265625000:ℝ)≤hardCoreMean G S (31/54:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point004
