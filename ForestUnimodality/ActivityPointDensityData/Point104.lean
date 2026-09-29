import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point104
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨97103/85225,287904869/1000000000,16653454550461/139715500000000,165853002242873807/1072698299250000000,72612273906994568031943380023/410999116637626255365000000000,16433127980416516106905278961/99424009583278869116375000000⟩
    path := ⟨22,712095131/424190262,41190147010986/24536692460525⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287904869/1000000000:ℝ)*S.card+(16433127980416516106905278961/99424009583278869116375000000:ℝ)≤hardCoreMean G S (97103/85225:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point104
