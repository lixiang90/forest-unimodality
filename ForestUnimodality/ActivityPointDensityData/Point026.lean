import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point026
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨581/635,134187779/500000000,49364561137/449250000000,12112897273/88246093750,4574390685038487797/28849689708500000000,13074882528365412151/90894664208187500000⟩
    path := ⟨18,365812221/231624442,134573800802/85209239665⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (134187779/500000000:ℝ)*S.card+(13074882528365412151/90894664208187500000:ℝ)≤hardCoreMean G S (581/635:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point026
