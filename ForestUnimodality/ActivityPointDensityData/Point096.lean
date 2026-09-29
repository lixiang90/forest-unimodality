import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point096
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨47887/42425,14354451/50000000,410579226251/3454975000000,2020602535949923/13129530337500000,216512191781186086233489127/1230170522800872765750000000,49028908574085529767412839/298297254909282488818750000⟩
    path := ⟨20,35645549/21291098,1019566809926/608987583675⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (14354451/50000000:ℝ)*S.card+(49028908574085529767412839/298297254909282488818750000:ℝ)≤hardCoreMean G S (47887/42425:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point096
