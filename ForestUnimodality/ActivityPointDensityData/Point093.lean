import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point093
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨95699/84925,71735929/250000000,4102462890933/34540375000000,20181143327762959/131242386187500000,8646014239086558611298538189/49158114837448756098750000000,3916182680303389945242000821/23850248060790312164093750000⟩
    path := ⟨20,178264071/106528142,10194636661258/6092173770325⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (71735929/250000000:ℝ)*S.card+(3916182680303389945242000821/23850248060790312164093750000:ℝ)≤hardCoreMean G S (95699/84925:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point093
