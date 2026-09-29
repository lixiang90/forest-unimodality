import ForestUnimodality.SharedAffineLaplace

namespace ForestUnimodality.SharedAffineData.EarlyStop20260928
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Tilt00
def retention : ℚ := (3/5)
def u : ℚ := (11/25)
def lo : ℚ := (64403642108314135853218403000896006087/100000000000000000000000000000000000000)
def hi : ℚ := (8050455263539266981652300375112000761/12500000000000000000000000000000000000)
def witness : ExpEnclosure.PowerCertificate := ⟨1, (-11/25), 40, (64403642108314135853218403000896006087/100000000000000000000000000000000000000), (8050455263539266981652300375112000761/12500000000000000000000000000000000000)⟩
theorem checked : witness.check (-u) lo hi=true := by decide +kernel
theorem admissible : 0≤u ∧ 0≤retention := by norm_num [u,retention]
theorem retention_bound : (retention:ℝ)≤Real.exp (-(u:ℝ)) := by
  have h := (witness.check_sound checked).1
  have hl : (retention:ℝ)≤lo := by norm_num [retention,lo]
  exact hl.trans (by simpa only [Rat.cast_neg] using h)
#print axioms checked
#print axioms admissible
#print axioms retention_bound
end Tilt00

namespace Decay00
def C : ℚ := (11258201/5000000)
def lo : ℚ := (37130862532458870665687596437614858189/100000000000000000000000000000000000000)
def hi : ℚ := (3713086253245887066568759643761485819/10000000000000000000000000000000000000)
def witness : ExpEnclosure.PowerCertificate := ⟨1, (-123840211/125000000), 40, (37130862532458870665687596437614858189/100000000000000000000000000000000000000), (3713086253245887066568759643761485819/10000000000000000000000000000000000000)⟩
theorem checked : witness.check (-C*Tilt00.u) lo hi=true := by decide +kernel
theorem decay_bound : Real.exp (-(C:ℝ)*(Tilt00.u:ℝ))≤(hi:ℝ) := by
  simpa only [Rat.cast_mul,Rat.cast_neg] using (witness.check_sound checked).2
#print axioms checked
#print axioms decay_bound
end Decay00

end ForestUnimodality.SharedAffineData.EarlyStop20260928
