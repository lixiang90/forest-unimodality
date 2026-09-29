import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point023
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨9/10,266873797/1000000000,381883421/3500000000,23887720709/175750000000,34338287409299/218633000000000,1531724252623/10767625000000⟩
    path := ⟨18,733126203/466252406,2098135827/1334368985⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (266873797/1000000000:ℝ)*S.card+(1531724252623/10767625000000:ℝ)≤hardCoreMean G S (9/10:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point023
