import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point092
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨47837/42475,35861909/125000000,1025338133559/8634312500000,5043212578098157/32806186781250000,540074462827373036880028843/3071367872856759883125000000,122316885563699393395891201/745179260408758503296875000⟩
    path := ⟨20,89138091/53276182,2548572718334/1523234584775⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (35861909/125000000:ℝ)*S.card+(122316885563699393395891201/745179260408758503296875000:ℝ)≤hardCoreMean G S (47837/42475:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point092
