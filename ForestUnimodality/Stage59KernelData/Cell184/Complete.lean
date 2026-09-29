import ForestUnimodality.Stage59KernelData.Cell184.Batch000_079

namespace ForestUnimodality.Stage59KernelData.Cell184
open FiniteMarginalSupport
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem residual_nonneg_of_degree_le79 (n : ℕ) (hn : n ≤ 79) (j : ℤ)
    (hs : geometrySupportCheck pairs n j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q := by
  interval_cases n
  · exact Degree000.actual_residual_nonneg j hs hq
  · exact Degree001.actual_residual_nonneg j hs hq
  · exact Degree002.actual_residual_nonneg j hs hq
  · exact Degree003.actual_residual_nonneg j hs hq
  · exact Degree004.actual_residual_nonneg j hs hq
  · exact Degree005.actual_residual_nonneg j hs hq
  · exact Degree006.actual_residual_nonneg j hs hq
  · exact Degree007.actual_residual_nonneg j hs hq
  · exact Degree008.actual_residual_nonneg j hs hq
  · exact Degree009.actual_residual_nonneg j hs hq
  · exact Degree010.actual_residual_nonneg j hs hq
  · exact Degree011.actual_residual_nonneg j hs hq
  · exact Degree012.actual_residual_nonneg j hs hq
  · exact Degree013.actual_residual_nonneg j hs hq
  · exact Degree014.actual_residual_nonneg j hs hq
  · exact Degree015.actual_residual_nonneg j hs hq
  · exact Degree016.actual_residual_nonneg j hs hq
  · exact Degree017.actual_residual_nonneg j hs hq
  · exact Degree018.actual_residual_nonneg j hs hq
  · exact Degree019.actual_residual_nonneg j hs hq
  · exact Degree020.actual_residual_nonneg j hs hq
  · exact Degree021.actual_residual_nonneg j hs hq
  · exact Degree022.actual_residual_nonneg j hs hq
  · exact Degree023.actual_residual_nonneg j hs hq
  · exact Degree024.actual_residual_nonneg j hs hq
  · exact Degree025.actual_residual_nonneg j hs hq
  · exact Degree026.actual_residual_nonneg j hs hq
  · exact Degree027.actual_residual_nonneg j hs hq
  · exact Degree028.actual_residual_nonneg j hs hq
  · exact Degree029.actual_residual_nonneg j hs hq
  · exact Degree030.actual_residual_nonneg j hs hq
  · exact Degree031.actual_residual_nonneg j hs hq
  · exact Degree032.actual_residual_nonneg j hs hq
  · exact Degree033.actual_residual_nonneg j hs hq
  · exact Degree034.actual_residual_nonneg j hs hq
  · exact Degree035.actual_residual_nonneg j hs hq
  · exact Degree036.actual_residual_nonneg j hs hq
  · exact Degree037.actual_residual_nonneg j hs hq
  · exact Degree038.actual_residual_nonneg j hs hq
  · exact Degree039.actual_residual_nonneg j hs hq
  · exact Degree040.actual_residual_nonneg j hs hq
  · exact Degree041.actual_residual_nonneg j hs hq
  · exact Degree042.actual_residual_nonneg j hs hq
  · exact Degree043.actual_residual_nonneg j hs hq
  · exact Degree044.actual_residual_nonneg j hs hq
  · exact Degree045.actual_residual_nonneg j hs hq
  · exact Degree046.actual_residual_nonneg j hs hq
  · exact Degree047.actual_residual_nonneg j hs hq
  · exact Degree048.actual_residual_nonneg j hs hq
  · exact Degree049.actual_residual_nonneg j hs hq
  · exact Degree050.actual_residual_nonneg j hs hq
  · exact Degree051.actual_residual_nonneg j hs hq
  · exact Degree052.actual_residual_nonneg j hs hq
  · exact Degree053.actual_residual_nonneg j hs hq
  · exact Degree054.actual_residual_nonneg j hs hq
  · exact Degree055.actual_residual_nonneg j hs hq
  · exact Degree056.actual_residual_nonneg j hs hq
  · exact Degree057.actual_residual_nonneg j hs hq
  · exact Degree058.actual_residual_nonneg j hs hq
  · exact Degree059.actual_residual_nonneg j hs hq
  · exact Degree060.actual_residual_nonneg j hs hq
  · exact Degree061.actual_residual_nonneg j hs hq
  · exact Degree062.actual_residual_nonneg j hs hq
  · exact Degree063.actual_residual_nonneg j hs hq
  · exact Degree064.actual_residual_nonneg j hs hq
  · exact Degree065.actual_residual_nonneg j hs hq
  · exact Degree066.actual_residual_nonneg j hs hq
  · exact Degree067.actual_residual_nonneg j hs hq
  · exact Degree068.actual_residual_nonneg j hs hq
  · exact Degree069.actual_residual_nonneg j hs hq
  · exact Degree070.actual_residual_nonneg j hs hq
  · exact Degree071.actual_residual_nonneg j hs hq
  · exact Degree072.actual_residual_nonneg j hs hq
  · exact Degree073.actual_residual_nonneg j hs hq
  · exact Degree074.actual_residual_nonneg j hs hq
  · exact Degree075.actual_residual_nonneg j hs hq
  · exact Degree076.actual_residual_nonneg j hs hq
  · exact Degree077.actual_residual_nonneg j hs hq
  · exact Degree078.actual_residual_nonneg j hs hq
  · exact Degree079.actual_residual_nonneg j hs hq

#print axioms residual_nonneg_of_degree_le79
end ForestUnimodality.Stage59KernelData.Cell184
