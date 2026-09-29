import ForestUnimodality.Stage80KernelData.Cell067.Batch000_098
import ForestUnimodality.FiniteKernelGraphBudget

namespace ForestUnimodality.Stage80KernelData.Cell067
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem residual_nonneg_of_degree_le98 (n : ℕ) (hn : n≤98) (j : ℤ)
    {q : ℝ} (hq : q∈Set.Icc (interval.lo:ℝ) (interval.hi:ℝ)) :
    0≤row.toReal.residual n j q := by
  interval_cases n
  · exact Kernel000.actual_residual_nonneg j hq
  · exact Kernel001.actual_residual_nonneg j hq
  · exact Kernel002.actual_residual_nonneg j hq
  · exact Kernel003.actual_residual_nonneg j hq
  · exact Kernel004.actual_residual_nonneg j hq
  · exact Kernel005.actual_residual_nonneg j hq
  · exact Kernel006.actual_residual_nonneg j hq
  · exact Kernel007.actual_residual_nonneg j hq
  · exact Kernel008.actual_residual_nonneg j hq
  · exact Kernel009.actual_residual_nonneg j hq
  · exact Kernel010.actual_residual_nonneg j hq
  · exact Kernel011.actual_residual_nonneg j hq
  · exact Kernel012.actual_residual_nonneg j hq
  · exact Kernel013.actual_residual_nonneg j hq
  · exact Kernel014.actual_residual_nonneg j hq
  · exact Kernel015.actual_residual_nonneg j hq
  · exact Kernel016.actual_residual_nonneg j hq
  · exact Kernel017.actual_residual_nonneg j hq
  · exact Kernel018.actual_residual_nonneg j hq
  · exact Kernel019.actual_residual_nonneg j hq
  · exact Kernel020.actual_residual_nonneg j hq
  · exact Kernel021.actual_residual_nonneg j hq
  · exact Kernel022.actual_residual_nonneg j hq
  · exact Kernel023.actual_residual_nonneg j hq
  · exact Kernel024.actual_residual_nonneg j hq
  · exact Kernel025.actual_residual_nonneg j hq
  · exact Kernel026.actual_residual_nonneg j hq
  · exact Kernel027.actual_residual_nonneg j hq
  · exact Kernel028.actual_residual_nonneg j hq
  · exact Kernel029.actual_residual_nonneg j hq
  · exact Kernel030.actual_residual_nonneg j hq
  · exact Kernel031.actual_residual_nonneg j hq
  · exact Kernel032.actual_residual_nonneg j hq
  · exact Kernel033.actual_residual_nonneg j hq
  · exact Kernel034.actual_residual_nonneg j hq
  · exact Kernel035.actual_residual_nonneg j hq
  · exact Kernel036.actual_residual_nonneg j hq
  · exact Kernel037.actual_residual_nonneg j hq
  · exact Kernel038.actual_residual_nonneg j hq
  · exact Kernel039.actual_residual_nonneg j hq
  · exact Kernel040.actual_residual_nonneg j hq
  · exact Kernel041.actual_residual_nonneg j hq
  · exact Kernel042.actual_residual_nonneg j hq
  · exact Kernel043.actual_residual_nonneg j hq
  · exact Kernel044.actual_residual_nonneg j hq
  · exact Kernel045.actual_residual_nonneg j hq
  · exact Kernel046.actual_residual_nonneg j hq
  · exact Kernel047.actual_residual_nonneg j hq
  · exact Kernel048.actual_residual_nonneg j hq
  · exact Kernel049.actual_residual_nonneg j hq
  · exact Kernel050.actual_residual_nonneg j hq
  · exact Kernel051.actual_residual_nonneg j hq
  · exact Kernel052.actual_residual_nonneg j hq
  · exact Kernel053.actual_residual_nonneg j hq
  · exact Kernel054.actual_residual_nonneg j hq
  · exact Kernel055.actual_residual_nonneg j hq
  · exact Kernel056.actual_residual_nonneg j hq
  · exact Kernel057.actual_residual_nonneg j hq
  · exact Kernel058.actual_residual_nonneg j hq
  · exact Kernel059.actual_residual_nonneg j hq
  · exact Kernel060.actual_residual_nonneg j hq
  · exact Kernel061.actual_residual_nonneg j hq
  · exact Kernel062.actual_residual_nonneg j hq
  · exact Kernel063.actual_residual_nonneg j hq
  · exact Kernel064.actual_residual_nonneg j hq
  · exact Kernel065.actual_residual_nonneg j hq
  · exact Kernel066.actual_residual_nonneg j hq
  · exact Kernel067.actual_residual_nonneg j hq
  · exact Kernel068.actual_residual_nonneg j hq
  · exact Kernel069.actual_residual_nonneg j hq
  · exact Kernel070.actual_residual_nonneg j hq
  · exact Kernel071.actual_residual_nonneg j hq
  · exact Kernel072.actual_residual_nonneg j hq
  · exact Kernel073.actual_residual_nonneg j hq
  · exact Kernel074.actual_residual_nonneg j hq
  · exact Kernel075.actual_residual_nonneg j hq
  · exact Kernel076.actual_residual_nonneg j hq
  · exact Kernel077.actual_residual_nonneg j hq
  · exact Kernel078.actual_residual_nonneg j hq
  · exact Kernel079.actual_residual_nonneg j hq
  · exact Kernel080.actual_residual_nonneg j hq
  · exact Kernel081.actual_residual_nonneg j hq
  · exact Kernel082.actual_residual_nonneg j hq
  · exact Kernel083.actual_residual_nonneg j hq
  · exact Kernel084.actual_residual_nonneg j hq
  · exact Kernel085.actual_residual_nonneg j hq
  · exact Kernel086.actual_residual_nonneg j hq
  · exact Kernel087.actual_residual_nonneg j hq
  · exact Kernel088.actual_residual_nonneg j hq
  · exact Kernel089.actual_residual_nonneg j hq
  · exact Kernel090.actual_residual_nonneg j hq
  · exact Kernel091.actual_residual_nonneg j hq
  · exact Kernel092.actual_residual_nonneg j hq
  · exact Kernel093.actual_residual_nonneg j hq
  · exact Kernel094.actual_residual_nonneg j hq
  · exact Kernel095.actual_residual_nonneg j hq
  · exact Kernel096.actual_residual_nonneg j hq
  · exact Kernel097.actual_residual_nonneg j hq
  · exact Kernel098.actual_residual_nonneg j hq

#print axioms residual_nonneg_of_degree_le98
end ForestUnimodality.Stage80KernelData.Cell067
