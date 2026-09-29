import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point086
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨23881/21275,143302257/500000000,2047342083491/17259250000000,10061550251405693/65559456375000000,269133431847441311969336933/1532643150766213027500000000,30483561705564280467536853/186083250142264985687500000⟩
    path := ⟨20,356697743/213395486,5096097601166/3048755517675⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143302257/500000000:ℝ)*S.card+(30483561705564280467536853/186083250142264985687500000:ℝ)≤hardCoreMean G S (23881/21275:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point086
