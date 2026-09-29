import ForestUnimodality.SelectionSourceCells
import Mathlib.Tactic.FinCases

/-! Exact parameters and full activity coverage for the frozen28 selection
rows. Source soundness is supplied separately by SelectionCertifiedLibrary. -/
namespace ForestUnimodality.SelectionSourceTable
structure Row where
  lower : ℚ
  upper : ℚ
  CJ : ℚ
  Cmu : ℚ

def row (i : Fin 28) : Row :=
  ![⟨(1/3), (1/2), 0, (2101229/2500000)⟩,
    ⟨(1/2), (7/10), (2056701/5000000), (524219/1000000)⟩,
    ⟨(7/10), (4/5), (1087053/2000000), (1527921/5000000)⟩,
    ⟨(4/5), (17/20), (293273/625000), (1405711/5000000)⟩,
    ⟨(17/20), (22/25), (5134821/10000000), (1169559/5000000)⟩,
    ⟨(22/25), (9/10), (2618077/5000000), (2157227/10000000)⟩,
    ⟨(9/10), (23/25), (5322049/10000000), (2073493/10000000)⟩,
    ⟨(23/25), (47/50), (2599103/5000000), (2097927/10000000)⟩,
    ⟨(47/50), (24/25), (1285141/2500000), (1045353/5000000)⟩,
    ⟨(24/25), (49/50), (5148663/10000000), (2050743/10000000)⟩,
    ⟨(49/50), 1, (5156403/10000000), (1006209/5000000)⟩,
    ⟨1, (51/50), (10667/20000), (59073/312500)⟩,
    ⟨(51/50), (26/25), (5338043/10000000), (231973/1250000)⟩,
    ⟨(26/25), (53/50), (5190199/10000000), (1898581/10000000)⟩,
    ⟨(53/50), (107/100), (5063543/10000000), (929757/5000000)⟩,
    ⟨(107/100), (27/25), (311643/625000), (1884421/10000000)⟩,
    ⟨(27/25), (109/100), (987739/2000000), (473691/2500000)⟩,
    ⟨(109/100), (11/10), (4815227/10000000), (974327/5000000)⟩,
    ⟨(11/10), (111/100), (4936143/10000000), (93469/500000)⟩,
    ⟨(111/100), (28/25), (40859/78125), (854693/5000000)⟩,
    ⟨(28/25), (113/100), (5224949/10000000), (42473/250000)⟩,
    ⟨(113/100), (57/50), (5222201/10000000), (1687563/10000000)⟩,
    ⟨(57/50), (29/25), (625997/1250000), (458077/2500000)⟩,
    ⟨(29/25), (6/5), (2494253/5000000), (119529/625000)⟩,
    ⟨(6/5), (13/10), (2458773/5000000), (2168711/10000000)⟩,
    ⟨(13/10), (3/2), (5388767/10000000), (2152601/10000000)⟩,
    ⟨(3/2), (9/5), (5340871/10000000), (2253533/10000000)⟩,
    ⟨(9/5), (9/4), (2812671/5000000), (2251111/10000000)⟩] i

def Row.CW (r : Row) : ℚ := r.CJ+2*r.Cmu

def rows : List Row := List.ofFn row

theorem row_parameters (i : Fin 28) :
    0<(row i).lower ∧ (row i).lower≤(row i).upper ∧ 0≤(row i).CJ ∧ 0≤(row i).Cmu := by
  fin_cases i <;> norm_num [row]

theorem intervalCoverage_checked :
    SourceIntervalCoverage.check Row.lower Row.upper (1/3) (9/4) rows=true := by
  decide +kernel

theorem covers {z : ℝ} (hlo : (1/3:ℝ)≤z) (hhi : z≤(9/4:ℝ)) :
    ∃i:Fin 28,((row i).lower:ℝ)≤z ∧ z≤((row i).upper:ℝ) := by
  obtain ⟨c,hmem,hcl,hch⟩ := SourceIntervalCoverage.check_sound_closed Row.lower Row.upper
    intervalCoverage_checked (by norm_num : (1/3:ℚ)<9/4)
    (by norm_num; exact hlo) (by norm_num; exact hhi)
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem
  exact ⟨i,hcl,hch⟩

#print axioms row_parameters
#print axioms covers
end ForestUnimodality.SelectionSourceTable
