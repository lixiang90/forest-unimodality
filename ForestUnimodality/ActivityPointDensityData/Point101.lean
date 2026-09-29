import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point101
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨24257/21325,287761147/1000000000,4160049254667/34919500000000,5176621997314963/33508467750000000,141587640339225548473645927/801947234230094145000000000,64093010218856133297657503/388157943779136506375000000⟩
    path := ⟨20,712238853/424477706,10296555714442/6136506459775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287761147/1000000000:ℝ)*S.card+(64093010218856133297657503/388157943779136506375000000:ℝ)≤hardCoreMean G S (24257/21325:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point101
