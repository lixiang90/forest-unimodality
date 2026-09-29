import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point061
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨11153/10375,282812891/1000000000,1910391909229/16340500000000,2213608865911523/14744661750000000,13301193165160603206570347/77152890237765615000000000,3022428820779267662776879/18940931388119816375000000⟩
    path := ⟨22,717187109/434374218,254977665966/154430723375⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (282812891/1000000000:ℝ)*S.card+(3022428820779267662776879/18940931388119816375000000:ℝ)≤hardCoreMean G S (11153/10375:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point061
