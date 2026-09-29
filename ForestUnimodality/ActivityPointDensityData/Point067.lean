import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point067
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨109/100,284032893/1000000000,9338770013/79500000000,3373552530001/22310750000000,958930885126958963/5528826957500000000,27209060233065427/169071470125000000⟩
    path := ⟨20,715967107/431934214,23540414663/14201644650⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (284032893/1000000000:ℝ)*S.card+(27209060233065427/169071470125000000:ℝ)≤hardCoreMean G S (109/100:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point067
