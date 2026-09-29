import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point014
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨67/86,15847273/62500000,35054997/343750000,85099145297/686109375000,2587677029630717/18031869187500000,1717335665391367/13366471257812500⟩
    path := ⟨16,46652727/30805454,1031982709/681432739⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (15847273/62500000:ℝ)*S.card+(1717335665391367/13366471257812500:ℝ)≤hardCoreMean G S (67/86:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point014
