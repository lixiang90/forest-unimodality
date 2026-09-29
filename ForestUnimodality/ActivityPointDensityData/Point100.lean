import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point100
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨12116/10675,287569457/1000000000,2077812964501/17453500000000,41345953862737799/267925298250000000,282553714018697863271012399/1601801474937345165000000000,3997578211199401431742723/24241773631624657625000000⟩
    path := ⟨20,712430543/424861086,5147616917976/3069803953475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287569457/1000000000:ℝ)*S.card+(3997578211199401431742723/24241773631624657625000000:ℝ)≤hardCoreMean G S (12116/10675:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point100
