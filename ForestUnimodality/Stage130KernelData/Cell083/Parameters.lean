import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-11315892310571706202892983/10000000000000000000000000)
  B := (90341757233095260071209509/1000000000000000000000000000)
  C := (2730734520612100590941651/1250000000000000000000000000)
  dδ := (71063048965195232953284687/1000000000000000000000000000)
  dM := (1097823475856210713452743/1000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(2590243764310008245388417/250000000000000000000000), (27043101799076701974300363/100000000000000000000000000), (12633627246467845850474987/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579/7004)
  hi := (5381/10506)
  vmin := (27577625/110376036)
  damping := (27577625/110376036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell083
