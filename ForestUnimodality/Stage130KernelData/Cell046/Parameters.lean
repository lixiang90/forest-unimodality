import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 83
  A := (-14806396488103425357252263/10000000000000000000000000)
  B := (12245893662625404949007013/125000000000000000000000000)
  C := (-26073686858863400102326313/10000000000000000000000000000)
  dδ := (4068530108365314007512481/62500000000000000000000000)
  dM := (10935456406194910689011479/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(8145938874723220868290241/1250000000000000000000000), (29982118428897805983979197/5000000000000000000000000), (68943706452583498389685701/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8999/18624)
  hi := (47/97)
  vmin := (86615375/346853376)
  damping := (86615375/346853376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell046
