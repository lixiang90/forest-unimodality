import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 5) where
  terms := Finset.univ
  scale := 114
  A := (9548242364233109292115387/50000000000000000000000000)
  B := (2106186016686781292683861/25000000000000000000000000)
  C := (15771656282939350290916991/25000000000000000000000000)
  dδ := (2749312710634089218508791/20000000000000000000000000)
  dM := (14405311932841440014652079/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(13809897388697146780600633/2000000000000000000000000), (13296629777647996917266937/5000000000000000000000000), (11465941998786703670543119/12500000000000000000000000), (22051703894033309438782453/1000000000000000000000000), (510262895429608231978591/25000000000000000000000)]
  retention := ![(4/5), (7/10), (3/5), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113/213)
  hi := (8069/15194)
  vmin := (57491625/230857636)
  damping := (57491625/230857636)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell149
