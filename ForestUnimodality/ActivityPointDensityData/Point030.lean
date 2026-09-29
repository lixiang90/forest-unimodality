import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point030
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨8999/9625,135169309/500000000,765718177493/6905750000000,23148855631829/166515656250000,85679054306377487898859/533796909797604500000000,735909109573453341332441/5042474277982453187500000⟩
    path := ⟨18,364830691/229661382,2066722776618/1301004599125⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (135169309/500000000:ℝ)*S.card+(735909109573453341332441/5042474277982453187500000:ℝ)≤hardCoreMean G S (8999/9625:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point030
