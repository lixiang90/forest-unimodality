import ForestUnimodality.Stage59KernelData.Cell080.Budget
import ForestUnimodality.MarkedAvailableWindow

namespace ForestUnimodality.Stage59KernelData.Cell080
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def availableWindow : MarkedAvailableWindow.Window := ⟨27,(49/99),(131/264),D⟩
theorem availableWindow_checked : availableWindow.check=true := by decide +kernel

variable {V : Type*} [DecidableEq V]
theorem available_profile_variance {G : SimpleGraph V} {S B : Finset V} {z : ℝ}
    (hB : IsMaximumMarginalIndependentOn G S B z) (hG : G.IsAcyclic)
    (hz : 0<z) (hq : z/(1+z)∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    hardCoreAvailableVariance G S B z≤(D:ℝ)*hardCoreAvailableMean G S B z := by
  exact availableWindow.actual_available_variance availableWindow_checked hB hG hz
    (by simpa only [availableWindow,interval] using hq)

#print axioms availableWindow_checked
#print axioms available_profile_variance
end ForestUnimodality.Stage59KernelData.Cell080
