import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point094
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨7977/7075,57398431/200000000,273571532501/2302900000000,448654155890941/2916889450000000,1335005871124561027134069/7588633788925981000000000,151166110423509713070379/920322504382512275000000⟩
    path := ⟨20,142601569/85203138,679665431826/406093899325⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (57398431/200000000:ℝ)*S.card+(151166110423509713070379/920322504382512275000000:ℝ)≤hardCoreMean G S (7977/7075:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point094
