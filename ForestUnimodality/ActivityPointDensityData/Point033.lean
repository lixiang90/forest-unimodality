import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point033
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨4631/4875,271777391/1000000000,788883023433/7068500000000,65186880060607/464605750000000,47234805707999115069369/291702621641081000000000,101557496289090607295139/688587846397646375000000⟩
    path := ⟨20,728222609/456445218,704599268186/441638260375⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (271777391/1000000000:ℝ)*S.card+(101557496289090607295139/688587846397646375000000:ℝ)≤hardCoreMean G S (4631/4875:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point033
