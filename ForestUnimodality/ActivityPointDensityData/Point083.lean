import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point083
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨95449/85175,143229537/500000000,8182692031799/69018250000000,40196462359037627/262131991125000000,17195638346716757663579717567/97991944027362446572500000000,7791559873109913906371583213/47610218969692301203187500000⟩
    path := ⟨20,356770463/213540926,20382267845774/12199575813975⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143229537/500000000:ℝ)*S.card+(7791559873109913906371583213/47610218969692301203187500000:ℝ)≤hardCoreMean G S (95449/85175:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point083
