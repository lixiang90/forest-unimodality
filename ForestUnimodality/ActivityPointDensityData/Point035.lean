import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point035
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨24/25,34090909/125000000,511363643/4562500000,20965909523/148531250000,404163736280881/2481660125000000,9059829900391/61004703125000⟩
    path := ⟨18,90909091/56818182,1363636368/852272725⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (34090909/125000000:ℝ)*S.card+(9059829900391/61004703125000:ℝ)≤hardCoreMean G S (24/25:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point035
