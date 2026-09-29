import ForestUnimodality.SelectionSourceTable
import ForestUnimodality.SelectionSourceData.Case01.Complete
import ForestUnimodality.SelectionSourceData.Case02.Complete
import ForestUnimodality.SelectionSourceData.Case03.Complete
import ForestUnimodality.SelectionSourceData.Case04.Complete
import ForestUnimodality.SelectionSourceData.Case05.Complete
import ForestUnimodality.SelectionSourceData.Case06.Complete
import ForestUnimodality.SelectionSourceData.Case07.Complete
import ForestUnimodality.SelectionSourceData.Case08.Complete
import ForestUnimodality.SelectionSourceData.Case09.Complete
import ForestUnimodality.SelectionSourceData.Case10.Complete
import ForestUnimodality.SelectionSourceData.Case11.Complete
import ForestUnimodality.SelectionSourceData.Case12.Complete
import ForestUnimodality.SelectionSourceData.Case13.Complete
import ForestUnimodality.SelectionSourceData.Case14.Complete
import ForestUnimodality.SelectionSourceData.Case15.Complete
import ForestUnimodality.SelectionSourceData.Case16.Complete
import ForestUnimodality.SelectionSourceData.Case17.Complete
import ForestUnimodality.SelectionSourceData.Case18.Complete
import ForestUnimodality.SelectionSourceData.Case19.Complete
import ForestUnimodality.SelectionSourceData.Case20.Complete
import ForestUnimodality.SelectionSourceData.Case21.Complete
import ForestUnimodality.SelectionSourceData.Case22.Complete
import ForestUnimodality.SelectionSourceData.Case23.Complete
import ForestUnimodality.SelectionSourceData.Case24.Complete
import ForestUnimodality.SelectionSourceData.Case25.Complete
import ForestUnimodality.SelectionSourceData.Case26.Complete
import ForestUnimodality.SelectionSourceData.Case27.Complete
import ForestUnimodality.SelectionSourceData.Case28.Complete

/-! The frozen 28 selection sources, checked over their complete continuous
probability, retention and response domains, with a uniform graph interface. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.SelectionCertifiedLibrary
open SelectionSourceTable
variable {V : Type*} [DecidableEq V]

theorem forest_variance (i : Fin 28) (G : SimpleGraph V) (hG : G.IsAcyclic)
    (S : Finset V) {z : ℝ}
    (hlo : ((row i).lower : ℝ) ≤ z) (hhi : z ≤ ((row i).upper : ℝ)) :
    hardCoreVariance G S z ≤
      ((row i).CJ : ℝ) * hardCoreMarginalSelectionScore G S z (row i).upper +
      ((row i).Cmu : ℝ) * hardCoreMean G S z := by
  fin_cases i
  · have hl : (1/3:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(1/2:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case01.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (1/2:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(7/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case02.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (7/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(4/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case03.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (4/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(17/20:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case04.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (17/20:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(22/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case05.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (22/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case06.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (9/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(23/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case07.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (23/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(47/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case08.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (47/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(24/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case09.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (24/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(49/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case10.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (49/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(1:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case11.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (1:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(51/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case12.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (51/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(26/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case13.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (26/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(53/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case14.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (53/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(107/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case15.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (107/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(27/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case16.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (27/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(109/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case17.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (109/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(11/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case18.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (11/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(111/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case19.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (111/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(28/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case20.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (28/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(113/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case21.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (113/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(57/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case22.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (57/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(29/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case23.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (29/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(6/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case24.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (6/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(13/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case25.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (13/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(3/2:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case26.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (3/2:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case27.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h
  · have hl : (9/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/4:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case28.forest_variance G hG S hl hh
    norm_num [row] at h ⊢
    exact h

/-- The score and the half-mean bound use this same actual maximum-marginal I. -/
theorem variance_le_mass (i : Fin 28) {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hlo : ((row i).lower : ℝ) ≤ z) (hhi : z ≤ ((row i).upper : ℝ)) :
    hardCoreVariance G S z ≤ ((row i).CW : ℝ) * hardCoreOccupiedMass G S I z := by
  fin_cases i
  · have hl : (1/3:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(1/2:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case01.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (1/2:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(7/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case02.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (7/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(4/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case03.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (4/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(17/20:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case04.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (17/20:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(22/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case05.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (22/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case06.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (9/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(23/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case07.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (23/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(47/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case08.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (47/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(24/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case09.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (24/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(49/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case10.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (49/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(1:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case11.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (1:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(51/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case12.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (51/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(26/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case13.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (26/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(53/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case14.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (53/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(107/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case15.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (107/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(27/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case16.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (27/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(109/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case17.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (109/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(11/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case18.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (11/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(111/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case19.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (111/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(28/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case20.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (28/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(113/100:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case21.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (113/100:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(57/50:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case22.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (57/50:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(29/25:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case23.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (29/25:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(6/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case24.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (6/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(13/10:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case25.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (13/10:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(3/2:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case26.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (3/2:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/5:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case27.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h
  · have hl : (9/5:ℝ)≤z := by simpa [row] using hlo
    have hh : z≤(9/4:ℝ) := by simpa [row] using hhi
    have h := SelectionSourceData.Case28.variance_le_mass hI hG hl hh
    norm_num [row, Row.CW] at h ⊢
    exact h

/-- Full activity coverage chooses a certified row; no finite-degree or size
hypothesis is needed for the source bound itself. -/
theorem exists_variance_le_mass {G : SimpleGraph V} {S I : Finset V} {z : ℝ}
    (hI : IsMaximumMarginalIndependentOn G S I z) (hG : G.IsAcyclic)
    (hlo : (1/3:ℝ)≤z) (hhi : z≤(9/4:ℝ)) :
    ∃i:Fin 28, ((row i).lower:ℝ)≤z ∧ z≤((row i).upper:ℝ) ∧
      hardCoreVariance G S z≤((row i).CW:ℝ)*hardCoreOccupiedMass G S I z := by
  obtain ⟨i,hil,hih⟩ := covers hlo hhi
  exact ⟨i,hil,hih,variance_le_mass i hI hG hil hih⟩

#print axioms forest_variance
#print axioms variance_le_mass
#print axioms exists_variance_le_mass
end ForestUnimodality.SelectionCertifiedLibrary
