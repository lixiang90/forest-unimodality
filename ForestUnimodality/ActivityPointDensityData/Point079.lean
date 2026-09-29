import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point079
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨94453/84475,286263711/1000000000,16193940423109/136690500000000,78759227477482379/514185952750000000,33042962851993521748968398531/188474773661454003995000000000,14974421819886028868727312259/91624047225534470716375000000⟩
    path := ⟨22,713736289/427472578,1302453787414/780068612475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (286263711/1000000000:ℝ)*S.card+(14974421819886028868727312259/91624047225534470716375000000:ℝ)≤hardCoreMean G S (94453/84475:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point079
