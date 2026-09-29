import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point009
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨103/152,48086269/200000000,1692557849/17900000000,132223729541/1175550000000,10893494052299573/83813580200000000,35996091537411919/311487153725000000⟩
    path := ⟨16,151913731/103827462,5347114293/3654556444⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (48086269/200000000:ℝ)*S.card+(35996091537411919/311487153725000000:ℝ)≤hardCoreMean G S (103/152:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point009
