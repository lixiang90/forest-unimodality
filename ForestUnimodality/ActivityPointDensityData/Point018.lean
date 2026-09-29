import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point018
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨1613/1865,32903791/125000000,34111800019/318187500000,1510323043797/11385015625000,12582652222288874889/82030494860125000000,205997569644544240899/1488207349397046875000⟩
    path := ⟨18,92096209/59192418,95477370234/61365570215⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (32903791/125000000:ℝ)*S.card+(205997569644544240899/1488207349397046875000:ℝ)≤hardCoreMean G S (1613/1865:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point018
