import ForestUnimodality.ActivityPointDensityForest

/-! Rational activity-point witness. All graph conclusions use the generic
all-order forest proof; the decision procedure is kernel evaluated. -/
namespace ForestUnimodality.ActivityPointDensityData.Point098
def certificate : ActivityPointDensity.Certificate :=
  { parameters := ⟨113/100,287185867/1000000000,9688703679/81500000000,3599611134431/23376750000000,1073056747125648997/6094084957500000000,30371854200507413/184663020125000000⟩
    path := ⟨22,712814133/425628266,24047997029/14359293350⟩ }
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked : certificate.check=true := by decide +kernel

theorem forest_density {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Finset V) (hn : 8≤S.card) :
    (287185867/1000000000:ℝ)*S.card+(30371854200507413/184663020125000000:ℝ)≤hardCoreMean G S (113/100:ℝ) := by
  simpa [certificate] using ActivityPointDensity.Certificate.forest_density
    (ActivityPointDensity.Certificate.check_sound checked) G hG S hn

#print axioms checked
#print axioms forest_density
end ForestUnimodality.ActivityPointDensityData.Point098
