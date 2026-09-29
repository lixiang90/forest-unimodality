import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point053
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨5381/5125,280731381/1000000000,921020550053/7943500000000,1035411914162419/6982550250000000,308795737381637482545991/1810681852161949000000000,167552986595532999663849/1065449077583771375000000⟩
    path := ⟨20,719268619/438537238,2359768877678/1438748327625⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (280731381/1000000000:ℝ)*S.card+(167552986595532999663849/1065449077583771375000000:ℝ)≤hardCoreMean G S (5381/5125:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point053
