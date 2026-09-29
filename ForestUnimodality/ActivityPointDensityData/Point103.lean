import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point103
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨48539/42625,143928483/500000000,4162259139451/34925750000000,41446491601485587/268138963875000000,4535779211350296355974517667/25679065370258396077500000000,513271468134574070109737247/3106421444581944230687500000⟩
    path := ⟨22,356071517/212143034,10297210727326/6134951587875⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (143928483/500000000:ℝ)*S.card+(513271468134574070109737247/3106421444581944230687500000:ℝ)≤hardCoreMean G S (48539/42625:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point103
