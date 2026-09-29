import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point062
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨22331/20725,141508871/500000000,1912659451923/16346750000000,2217543935860901/14753071125000000,53333605131383035762523681/309043988225030272500000000,24233701464342500339598859/151650691412744398187500000⟩
    path := ⟨20,358491129/216982258,4845430803398/2932771351475⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (141508871/500000000:ℝ)*S.card+(24233701464342500339598859/151650691412744398187500000:ℝ)≤hardCoreMean G S (22331/20725:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point062
